import os
import subprocess


def cnt(result):  # 将结果转化为整数
    result.reverse()
    sums = 0
    for i in range(len(result)):
        if result[i] > 0:
            sums += 2 ** i
    return sums


def list_to_int(result, obj_type):
    res = []
    for i in range(len(result)):
        score = cnt(result[i])
        if obj_type[i] == 1:
            res.append(score)
        else:
            score = 2 ** len(result[i]) - 1 - score
            res.append(score)
    return res


def assum_in_m(assum, m):
    for i in assum:
        if i not in m:
            return False
    return True


def cnf_from_z3(constraint_file):
    path = os.getcwd()
    path = os.path.dirname(os.path.dirname(os.path.dirname(path)))
    try:
        command = [path + '/z3/build/z3', "opt.priority=box", constraint_file]
        result = subprocess.run(command,
                                capture_output=True,
                                text=True,
                                check=True)
        # 获取 Z3 的输出
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running Z3: {e}")
        return None


def read_cnf(data):
    lines = data.splitlines()

    clauses = []
    obj_type = []  # 0为最小化，1为最大化
    soft = []
    con = '0'
    soft_temp = []

    # 处理首行获得子句数量
    l = lines[0].strip()
    parts = l.split()
    num_clauses = int(parts[3])

    # 处理子句
    i = 1
    while i <= num_clauses:
        clause = list(map(int, lines[i].split()))
        clause.pop()
        clauses.append(clause)
        i += 1

    j = i
    dic = {}
    mi = 10 ** 10
    while lines[j].startswith('c'):
        if len(lines[j].split()) < 6:
            j += 1
            continue
        p = lines[j].split('!')
        try:
            dic[int(p[-1])] = lines[j]
        except Exception as e:
            print(lines[j], e)
            return None
        if int(p[-1]) < mi:
            mi = int(p[-1])
        j += 1

    for k, line in dic.items():
        lines[i + k - mi] = line
    l = len(dic)
    for k in range(l):
        parts = lines[i + k].split()
        if len(parts) < 6:
            break

        if parts[4].endswith(':0]'):
            if len(soft_temp):
                soft.append(soft_temp)
                soft_temp = []
                obj_type.append(int(con))
        con = parts[3][3]
        soft_temp.append(int(parts[1]))

    if len(soft_temp):
        soft.append(soft_temp)
        obj_type.append(int(con))

    return clauses, soft, obj_type


def res_z3_trans(r_z3):
    lines = r_z3.splitlines()
    i = 2
    l = len(lines)
    r = []
    while i < l:
        parts = lines[i].split()
        if len(parts) > 1:
            r.append(int(parts[1][0:-1]))
        i += 1
    return r


if __name__ == '__main__':
    res_z3 = subprocess.run(['z3', 'opt.priority=box', '/arlib/benchmarks/omt/'],
                            capture_output=True,
                            text=True,
                            check=True).stdout
    print(res_z3_trans(res_z3))
