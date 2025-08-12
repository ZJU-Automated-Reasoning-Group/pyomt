import os
import tempfile
import textwrap
import subprocess
import sys


def write_wcnf(tmpdir: str, content: str) -> str:
    path = os.path.join(tmpdir, "toy.wcnf")
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    return path


def test_cli_info_runs_and_prints_stats():
    wcnf_text = textwrap.dedent(
        """
        p wcnf 3 4 3
        1 1 0
        1 2 0
        1 3 0
        3 -1 -2 -3 0
        """
    ).strip() + "\n"

    with tempfile.TemporaryDirectory() as tmp:
        wpath = write_wcnf(tmp, wcnf_text)
        # Run as module to execute click app
        cmd = [sys.executable, "-m", "pyomt.cli.maxsat", "info", wpath]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        out = proc.stdout.decode("utf-8")
        assert "Number of variables" in out


def test_cli_solve_runs_fm_engine():
    wcnf_text = textwrap.dedent(
        """
        p wcnf 1 2 2
        1 1 0
        2 -1 0
        """
    ).strip() + "\n"

    with tempfile.TemporaryDirectory() as tmp:
        wpath = write_wcnf(tmp, wcnf_text)
        cmd = [sys.executable, "-m", "pyomt.cli.maxsat", "solve", wpath, "--engine", "FM"]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        out = proc.stdout.decode("utf-8")
        # Should at least print a status line
        assert "Status:" in out or "Optimal solution found" in out

