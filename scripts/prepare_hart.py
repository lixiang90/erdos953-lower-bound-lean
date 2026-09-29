"""Fetch Hart's pinned upstream proof and apply Lean 4.32.2 compatibility edits.

Hart's source is not stored in this repository.  The generated files under
Erdos953Formalization/ remain ignored by Git and retain Hart's authorship.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HART_URL = "https://github.com/AllenGrahamHart/FormalConjectures-Bench.git"
HART_COMMIT = "0d031f7212150df788f4fa38c26cfc3fc729f3d0"
MODULE_DIR = Path("formalizations/erdos953/Erdos953Formalization")


def run(*args: str, cwd: Path | None = None) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(f"{' '.join(args)} failed:\n{result.stderr}")
    return result.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--hart-checkout",
        type=Path,
        help="Use an existing checkout at the pinned Hart commit instead of cloning.",
    )
    args = parser.parse_args()

    checkout = args.hart_checkout or ROOT / ".upstream-hart"
    if not checkout.is_dir():
        run("git", "clone", "--filter=blob:none", "--no-checkout", HART_URL, str(checkout))
    if args.hart_checkout:
        actual = run("git", "rev-parse", "HEAD", cwd=checkout)
        if actual != HART_COMMIT:
            parser.error(f"Hart checkout is {actual}, expected {HART_COMMIT}")
    else:
        run("git", "sparse-checkout", "init", "--cone", cwd=checkout)
        run("git", "sparse-checkout", "set", str(MODULE_DIR).replace('\\', '/'), cwd=checkout)
        run("git", "checkout", "--force", "--detach", HART_COMMIT, cwd=checkout)

    source = checkout / MODULE_DIR
    if not source.is_dir():
        parser.error(f"Missing Hart proof source: {source}")
    target = ROOT / "Erdos953Formalization"
    target.mkdir(exist_ok=True)
    for original in sorted(source.glob("*.lean")):
        shutil.copy2(original, target / original.name)

    patch = ROOT / "patches" / "hart-lean-4.32.2.patch"
    run("git", "apply", "--unidiff-zero", "--check", str(patch), cwd=ROOT)
    run("git", "apply", "--unidiff-zero", str(patch), cwd=ROOT)
    print(f"Prepared {len(list(source.glob('*.lean')))} Hart modules at {HART_COMMIT}")
    print("Applied attributed Lean 4.32.2 compatibility patch; generated files are Git-ignored.")


if __name__ == "__main__":
    main()
