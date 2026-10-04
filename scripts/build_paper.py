"""Build the standalone paper, resolving all LaTeX citations and references."""
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main() -> None:
    paper = Path(__file__).resolve().parents[1] / "paper"
    stem = "retreat-uniform-lower-bound"
    compiler = shutil.which("pdflatex")
    if compiler is None and sys.platform == "win32":
        candidate = Path.home() / "AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe"
        if candidate.is_file():
            compiler = str(candidate)
    if compiler is None:
        raise SystemExit("An existing pdflatex installation is required.")
    command = [compiler, "-interaction=nonstopmode", "-halt-on-error", "-no-shell-escape"]
    if "miktex" in compiler.lower():
        command.append("-enable-installer=no")
    command.append(stem + ".tex")
    unsettled = re.compile(
        r"(?:Citation|Reference) .+? undefined|There were undefined references|"
        r"Label\(s\) may have changed|Rerun to get|rerunfilecheck Warning|"
        r"multiply[- ]defined labels", re.IGNORECASE
    )
    for count in range(1, 5):
        result = subprocess.run(command, cwd=paper, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, errors="replace")
        log = (paper / (stem + ".log")).read_text(encoding="utf-8", errors="replace")
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
        if count >= 2 and not unsettled.search(log):
            print(f"Built {paper / (stem + '.pdf')} in {count} passes; all references resolved.")
            overflow = re.findall(r"Overfull .+", log)
            if overflow:
                print("Layout warnings:", *overflow, sep="\n")
            return
    raise SystemExit("Unresolved or duplicate LaTeX references remain after four passes.")


if __name__ == "__main__":
    main()
