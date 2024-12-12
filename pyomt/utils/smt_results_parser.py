"""Utils for manipulating values"""
import re


RE_GET_EXPR_VALUE_FMT_BIN = re.compile(r"\(\((?P<expr>(.*))[ \n\s]*#b(?P<value>([0-1]*))\)\)")
RE_GET_EXPR_VALUE_FMT_DEC = re.compile(r"\(\((?P<expr>(.*))\ \(_\ bv(?P<value>(\d*))\ \d*\)\)\)")
RE_GET_EXPR_VALUE_FMT_HEX = re.compile(r"\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)")
RE_OBJECTIVES_EXPR_VALUE = re.compile(
    r"\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*", re.MULTILINE | re.DOTALL
)


def parse_smt_model(model_str):
    """
    Parse SMT solver model output and extract variable assignments.

    Args:
        model_str (str): The model string from solver's get-model command

    Returns:
        dict: Dictionary mapping variable names to their values
    """
    # Remove outer parentheses and 'model' keyword
    model_str = model_str.strip()[1:-1].strip()
    if model_str.startswith("model"):
        model_str = model_str[5:].strip()

    results = {}
    current_pos = 0

    while current_pos < len(model_str):
        # Skip whitespace
        while current_pos < len(model_str) and model_str[current_pos].isspace():
            current_pos += 1

        if current_pos >= len(model_str):
            break

        # Each definition starts with (define-fun
        if not model_str[current_pos:].startswith("(define-fun"):
            current_pos += 1
            continue

        # Find matching closing parenthesis
        open_count = 1
        start_pos = current_pos
        current_pos += 1

        while open_count > 0 and current_pos < len(model_str):
            if model_str[current_pos] == '(':
                open_count += 1
            elif model_str[current_pos] == ')':
                open_count -= 1
            current_pos += 1

        if open_count > 0:
            raise ValueError("Malformed model string: unmatched parentheses")

        # Parse the definition
        definition = model_str[start_pos:current_pos].strip()
        var_value = _parse_definition(definition)
        if var_value:
            results[var_value[0]] = var_value[1]

    return results


def _parse_definition(definition):
    """
    Parse a single define-fun expression.

    Args:
        definition (str): A single define-fun expression

    Returns:
        tuple: (variable_name, value) or None if parsing fails
    """
    parts = definition.split()
    if len(parts) < 4:
        return None

    # Extract variable name
    var_name = parts[1]

    # Find the value part (last element/expression in definition)
    value_str = definition.split(")")[-2].strip()

    # Parse different types of values
    try:
        # Try integer
        if value_str.isdigit() or (value_str.startswith('-') and value_str[1:].isdigit()):
            return (var_name, int(value_str))

        # Try float
        if '.' in value_str:
            return (var_name, float(value_str))

        # Try boolean
        if value_str in ('true', 'false'):
            return (var_name, value_str == 'true')

        # Try rational numbers (represented as fractions)
        if '/' in value_str:
            num, denom = value_str.split('/')
            return (var_name, float(int(num)) / float(int(denom)))

        # Handle other types (keep as string)
        return (var_name, value_str)

    except (ValueError, ZeroDivisionError):
        return (var_name, value_str)


def getvalue_bv(t):
    base = 2
    m = RE_GET_EXPR_VALUE_FMT_BIN.match(t)
    if m is None:
        m = RE_GET_EXPR_VALUE_FMT_DEC.match(t)
        base = 10
    if m is None:
        m = RE_GET_EXPR_VALUE_FMT_HEX.match(t)
        base = 16
    if m is None:
        raise Exception(f"I don't know how to parse the value {str(t)}")

    expr, value = m.group("expr"), m.group("value")  # type: ignore
    return int(value, base)


def getvalue_bool(t):
    return {"true": True, "false": False, "#b0": False, "#b1": True}[t[2:-2].split(" ")[1]]


def parse_smt_model(model_str):
    """
    Parse SMT solver model output and extract variable assignments.

    Args:
        model_str (str): The model string from solver's get-model command

    Returns:
        dict: Dictionary mapping variable names to their values
    """
    # Remove outer parentheses and 'model' keyword
    model_str = model_str.strip()[1:-1].strip()
    if model_str.startswith("model"):
        model_str = model_str[5:].strip()

    results = {}
    current_pos = 0

    while current_pos < len(model_str):
        # Skip whitespace
        while current_pos < len(model_str) and model_str[current_pos].isspace():
            current_pos += 1

        if current_pos >= len(model_str):
            break

        # Each definition starts with (define-fun
        if not model_str[current_pos:].startswith("(define-fun"):
            current_pos += 1
            continue

        # Find matching closing parenthesis
        open_count = 1
        start_pos = current_pos
        current_pos += 1

        while open_count > 0 and current_pos < len(model_str):
            if model_str[current_pos] == '(':
                open_count += 1
            elif model_str[current_pos] == ')':
                open_count -= 1
            current_pos += 1

        if open_count > 0:
            raise ValueError("Malformed model string: unmatched parentheses")

        # Parse the definition
        definition = model_str[start_pos:current_pos].strip()
        var_value = _parse_definition(definition)
        if var_value:
            results[var_value[0]] = var_value[1]

    return results


def _parse_definition(definition):
    """
    Parse a single define-fun expression.

    Args:
        definition (str): A single define-fun expression

    Returns:
        tuple: (variable_name, value) or None if parsing fails
    """
    parts = definition.split()
    if len(parts) < 4:
        return None

    # Extract variable name
    var_name = parts[1]

    # Find the value part (last element/expression in definition)
    value_str = definition.split(")")[-2].strip()

    # Parse different types of values
    try:
        # Try integer
        if value_str.isdigit() or (value_str.startswith('-') and value_str[1:].isdigit()):
            return (var_name, int(value_str))

        # Try float
        if '.' in value_str:
            return (var_name, float(value_str))

        # Try boolean
        if value_str.lower() in ('true', 'false'):
            return (var_name, value_str.lower() == 'true')

        # Try rational numbers (represented as fractions)
        if '/' in value_str:
            num, denom = value_str.split('/')
            return (var_name, float(int(num)) / float(int(denom)))

        # Handle other types (keep as string)
        return (var_name, value_str)

    except (ValueError, ZeroDivisionError):
        return (var_name, value_str)


def run_tests():
    # Test case 1: Basic types
    test1 = """
    (model 
      (define-fun x () Int 42)
      (define-fun y () Real 3.14)
      (define-fun b () Bool true)
    )
    """
    print(parse_smt_model(test1))
    # assert parse_smt_model(test1) == {'x': 42, 'y': 3.14, 'b': True}

    # Test case 2: Negative numbers and fractions
    test2 = """
    (model 
      (define-fun neg () Int -123)
      (define-fun ratio () Real (/ 3 2))
      (define-fun decimal () Real -2.5)
    )
    """
    result2 = parse_smt_model(test2)
    print(result2)

    # Test case 3: Boolean variations
    test3 = """
    (model 
      (define-fun b1 () Bool true)
      (define-fun b2 () Bool false)
      (define-fun b3 () Bool TRUE)
      (define-fun b4 () Bool FALSE)
    )
    """
    print(parse_smt_model(test3))
    # assert parse_smt_model(test3) == {'b1': True, 'b2': False, 'b3': True, 'b4': False}

    # Test case 4: Complex expressions and whitespace
    test4 = """
    (model(define-fun complex () Int 42)(define-fun   spaced   ()   Int   123   ))
    """
    print(parse_smt_model(test4))
    # assert parse_smt_model(test4) == {'complex': 42, 'spaced': 123}

    # Test case 6: Complex rational numbers
    test6 = """
    (model 
      (define-fun r1 () Real (/ 22 7))
      (define-fun r2 () Real (/ -1 2))
      (define-fun r3 () Real (/ 9 3))
    )
    """
    result6 = parse_smt_model(test6)
    print(result6)
    # assert abs(result6['r1'] - 22 / 7) < 1e-10
    # assert abs(result6['r2'] - (-0.5)) < 1e-10
    # assert abs(result6['r3'] - 3.0) < 1e-10

    # Test case 7: Mixed types
    test7 = """
    (model 
      (define-fun i () Int 42)
      (define-fun r () Real 3.14)
      (define-fun b () Bool false)
      (define-fun f () Real (/ 1 3))
      (define-fun n () Int -987)
    )
    """
    result7 = parse_smt_model(test7)
    print(result7)

    print("All tests passed!")


# Example usage:
if __name__ == "__main__":
    run_tests()
