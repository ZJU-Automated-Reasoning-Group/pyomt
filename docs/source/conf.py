import os
import sys

# Ensure project root is on sys.path so autodoc can import the package
# docs/source/conf.py → project_root is two levels up
sys.path.insert(0, os.path.abspath(os.path.join(__file__, "../..", "..")))

# -- Project information -----------------------------------------------------

project = "pyomt"
copyright = "2025, rainoftime"
author = "rainoftime"

# The full version, including alpha/beta/rc tags
release = "v0.1"

# General configuration
extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.autosummary',
    'sphinx.ext.napoleon',
    'sphinx.ext.viewcode',
    'sphinx.ext.githubpages',
    'sphinx_rtd_theme'
]

# Autosummary/autodoc configuration
autosummary_generate = True
autodoc_default_options = {
    'members': True,
    'undoc-members': True,
    'show-inheritance': True,
}
autodoc_typehints = 'description'

# Avoid importing heavy optional deps at doc-build time
autodoc_mock_imports = [
    'z3',
    'z3-solver',
    'pysmt',
    'pysmt.shortcuts',
    'pysmt.typing',
]

# Alternative themes you could use instead:
# For alabaster theme (built-in)
# html_theme = 'alabaster'

# For classic theme (built-in)
# html_theme = 'classic'

# For nature theme (built-in)
# html_theme = 'nature'

templates_path = ['_templates']
exclude_patterns = []

# HTML output options
html_theme = 'sphinx_rtd_theme'  # ReadTheDocs theme
# html_static_path = ['_static']
html_title = 'pyomt Documentation'

# LaTeX output options
latex_elements = {
    'papersize': 'letterpaper',
    'pointsize': '10pt',
}
