# Mark this package as typed for type checkers
try:
    import importlib.resources as _ilr  # noqa: F401
except Exception:
    # Fallback for very old Python versions
    pass


