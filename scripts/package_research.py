"""Publish an owned Erdős 953 research snapshot, keeping all original bytes.

Run from this repository after placing the workspace outputs in ../research,
or pass --source and --destination. Third-party checkouts are never traversed.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import re
import shutil
import zipfile

PREFIXES = ("erdos953", "verify_953", "summarize_953", "plot_953", "analyze_953")
STAMP = "2026-10-03"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package(source, destination):
    source, destination = source.resolve(), destination.resolve()
    assert source != destination
    files = sorted(p for p in source.iterdir() if p.is_file() and p.name.startswith(PREFIXES))
    assert files and not any(p.stat().st_size > 100_000_000 for p in files)
    # Never collect a directory recursively: upstream clones, caches, account
    # exports, other problems, and build dependencies are outside this snapshot.
    for p in files:
        if p.suffix in (".py", ".json", ".txt", ".md", ".log"):
            assert not re.search(r"(?:ghp_|github_pat_|gho_|sk-proj-)[A-Za-z0-9_]{20,}", p.read_text(encoding="utf-8", errors="replace")), p.name
    local_names = {p.name for p in files}
    missing_imports = set()
    for p in files:
        if p.suffix == ".py":
            tree = ast.parse(p.read_text(encoding="utf-8-sig"), filename=p.name)
            for node in ast.walk(tree):
                names = [node.module] if isinstance(node, ast.ImportFrom) else [n.name for n in node.names] if isinstance(node, ast.Import) else []
                for name in names:
                    if name and name.startswith(PREFIXES) and name.split(".")[0]+".py" not in local_names:
                        missing_imports.add(name)
    assert not missing_imports, missing_imports
    destination.mkdir(parents=True, exist_ok=True)
    archive_dir = destination/"archives"
    archive_dir.mkdir(exist_ok=True)
    archive = archive_dir/f"erdos953-research-snapshot-{STAMP}.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in files:
            z.write(p, p.name)
    assert archive.stat().st_size < 100_000_000
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert set(z.namelist()) == local_names
        for p in files:
            assert hashlib.sha256(z.read(p.name)).hexdigest() == digest(p)
    # Keep code, conclusions, audit reports and latest lower-bound certificates
    # directly readable. The complete data for earlier experiments is in ZIP.
    visible = [p for p in files if p.suffix in (".py", ".txt", ".md", ".png", ".svg", ".log")
        or any(tag in p.name for tag in ("audit", "summary", "current-certified", "Ainfty", "iterated-ring", "ring-exchange", "explicit-constants"))]
    for p in visible:
        shutil.copyfile(p, destination/p.name)
    manifest = {"date": STAMP, "scope": "Erdos 953 research outputs authored or generated in this workspace; third-party repositories excluded",
        "archive": archive.relative_to(destination).as_posix(), "archive_sha256": digest(archive),
        "archive_bytes": archive.stat().st_size, "file_count": len(files),
        "uncompressed_bytes": sum(p.stat().st_size for p in files),
        "directly_browsable_file_count": len(visible),
        "files": [{"name": p.name, "bytes": p.stat().st_size, "sha256": digest(p),
            "directly_browsable": p in visible} for p in files]}
    (destination/f"snapshot-manifest-{STAMP}.json").write_text(json.dumps(manifest, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in manifest.items() if k != "files"}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    repo = Path(__file__).resolve().parents[1]
    parser.add_argument("--source", type=Path, default=repo.parent/"research")
    parser.add_argument("--destination", type=Path, default=repo/"research")
    args = parser.parse_args()
    package(args.source, args.destination)
