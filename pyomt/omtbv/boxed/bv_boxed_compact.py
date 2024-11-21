import os
import subprocess
import time

from pyomt.omtbv.bv_opt_utils import cnt, res_z3_trans
from pysmt.shortcuts import *
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand


# 新建一个parser，以过滤掉maximize、minimize和get-objectives指令
class TSSmtLibParser(SmtLibParser):
    def __init__(self, env=None, interactive=False):
        SmtLibParser.__init__(self, env, interactive)

        # Add new commands
        #
        # The mapping function takes care of consuming the command
        # name from the input stream, e.g., '(init' . Therefore,
        # _cmd_init will receive the rest of the stream, in our
        # example, '(and A B)) ...'
        self.commands["maximize"] = self._cmd_maximize
        self.commands["minimize"] = self._cmd_minimize
        self.commands["get-objectives"] = self._cmd_get_objs

        # Remove unused commands
        #
        # If some commands are not compatible with the extension, they
        # can be removed from the parser. If found, they will cause
        # the raising of the exception UnknownSmtLibCommandError
        del self.commands["get-value"]

    def _cmd_maximize(self, current, tokens):
        # This cmd performs the parsing of:
        #   <expr> )
        # and returns a new SmtLibCommand
        expr = self.get_expression(tokens)
        self.consume_closing(tokens, current)
        return SmtLibCommand(name="maximize", args=(expr,))

    def _cmd_minimize(self, current, tokens):
        # This performs the same parsing as _cmd_init, but returns a
        # different object. The parser is not restricted to return
        # SmtLibCommand, but using them makes handling them
        # afterwards easier.
        expr = self.get_expression(tokens)
        self.consume_closing(tokens, current)
        return SmtLibCommand(name="minimize", args=(expr,))

    def _cmd_get_objs(self, current, tokens):
        self.consume_closing(tokens, current)
        return SmtLibCommand(name="get-objectives", args=())


# 从文件中获取约束子句和最优化目标
def get_input(file):
    ts_parser = TSSmtLibParser()
    script = ts_parser.get_script_fname(file)
    stack = []
    objs = []
    _And = get_env().formula_manager.And

    for cmd in script:
        if cmd.name == 'assert':
            stack.append(cmd.args[0])
        if cmd.name == 'maximize':
            objs.append([cmd.args[0], 1])
        if cmd.name == 'minimize':
            objs.append([cmd.args[0], 0])
    ori_formula = _And(stack)
    return ori_formula, objs


def map_bitvector(input_vars):  # 将所有位向量目标的每一位都创建对应布尔变量
    bv2bool = {}  # for tracking what Bools corresponding to a bv
    for var in input_vars:
        if var[0].get_type() != BOOL:
            name = var[0]
            size = var[0].symbol_type().width
            bool_vars = []
            if var[1] == 1:
                for i in range(size):
                    x = size - 1 - i  # 位向量最低位为0，最高位为size-1，这样从高位到低位储存
                    v = Equals(BVExtract(var[0], x, x), BV(1, 1))
                    bool_vars.append(v)
                bv2bool[str(name)] = bool_vars
            else:
                for i in range(size):
                    x = size - 1 - i
                    v = Equals(BVExtract(var[0], x, x), BV(0, 1))
                    bool_vars.append(v)
                bv2bool['-' + str(name)] = bool_vars
    objectives = []
    for key, value in bv2bool.items():
        objectives.append(value)
    # print(clauses)
    return objectives


def check_assum(model, assums_obj, unsol, objectives):
    ass_index = []
    for i in unsol:
        sat = True
        assums = assums_obj[i] + [1]
        for j in range(len(assums)):
            if assums[j] and model[objectives[i][j]].is_false():
                sat = False
                break
        if sat:
            ass_index.append(i)
    return ass_index


def solve(formula, objectives):
    s = Solver()
    s.add_assertion(formula)
    unsol = list(range(len(objs)))
    result = list([list() for _ in range(len(objs))])
    res_clause = list([list() for _ in range(len(objs))])  # 存储已判定目标的结果
    while len(unsol):  # 还有未解决的目标时
        # print('unsol: ', unsol)
        assumption = {}  # 将未解决的目标和下一位作为assumption保存
        for i in unsol:
            obj = objectives[i][len(result[i])]  # 获取目标待求下一位
            if not res_clause[i]:
                assum = obj
            else:
                assum = And(res_clause[i], obj)
            assumption[i] = assum
        while len(assumption):
            a = 1
            for key, value in assumption.items():
                if a == 1:
                    a = value
                else:
                    a = Or(a, value)
            s.push()
            s.add_assertion(a)
            if s.solve():
                m = s.get_model()
                assum_index = check_assum(m, result, unsol, objectives)  # 检查哪些assum是可满足的，返回可满足assum的下标
                s.pop()
                for i in assum_index:  # 可满足的下标里结果更新true， 并选下一位
                    obj = objectives[i][len(result[i])]
                    result[i].append(1)
                    if not res_clause[i]:
                        res_clause[i] = obj
                    else:
                        res_clause[i] = And(res_clause[i], obj)
                    if len(result[i]) == len(objectives[i]):
                        unsol.remove(i)
                        assumption.pop(i)
                    else:
                        obj = objectives[i][len(result[i])]
                        assumption[i] = And(assumption[i], obj)
            else:
                s.pop()
                finish = []
                for i in unsol:
                    result[i].append(0)
                    if len(result[i]) == len(objectives[i]):
                        finish.append(i)
                for i in finish:
                    unsol.remove(i)
                    assumption.pop(i)
                break
    return result


def res_2int(result, objectives):
    res_int = []
    for i in range(len(objectives)):
        score = cnt(result[i])
        if objectives[i][1] == 1:
            res_int.append(score)
        else:
            l = len(result[i])
            score = 2 ** l - 1 - score
            res_int.append(score)
    return res_int


if __name__ == '__main__':
    path = os.getcwd()
    path = os.path.dirname(path)
    path = os.path.dirname(path)
    path = os.path.dirname(path)

    file_1 = r'benchmarks/omt/clearblue/case30515550.smt2'
    filename = os.path.join(path, file_1)

    formu, objec = get_input(filename)
    objs = map_bitvector(objec)
    t = time.time()
    r = solve(formu, objs)
    r = res_2int(r, objec)
    print(r)
    # solve(formula, objs, res, res_cla, unsolved)
    print('t:', time.time() - t)

    t = time.time()
    res_z3 = subprocess.run(['z3', 'opt.priority=box', filename],
                            capture_output=True,
                            text=True,
                            check=True).stdout
    t = time.time() - t
    print('t_z3:', t)
    print(res_z3)
    print(res_z3_trans(res_z3) == r)
