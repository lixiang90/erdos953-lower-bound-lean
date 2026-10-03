"""Check the published snapshot hashes, or the staged Git blobs before upload."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "research/snapshot-manifest-2026-10-03.json"


def run(index=False):
    def contents(name):
        if index:
            return subprocess.check_output(["git", "cat-file", "blob", ":"+name], cwd=ROOT)
        return (ROOT/name).read_bytes()
    manifest = json.loads(contents(MANIFEST))
    archive = "research/"+manifest["archive"]
    assert hashlib.sha256(contents(archive)).hexdigest() == manifest["archive_sha256"]
    checked = 0
    for f in manifest["files"]:
        if f["directly_browsable"]:
            data = contents("research/"+f["name"])
            assert len(data) == f["bytes"], f["name"]
            assert hashlib.sha256(data).hexdigest() == f["sha256"], f["name"]
            checked += 1
    print(json.dumps({"all_passed": True, "source": "Git index" if index else "working checkout",
        "directly_browsable_files_checked": checked, "archive_sha256": manifest["archive_sha256"],
        "archived_files": manifest["file_count"]}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git-index", action="store_true")
    run(parser.parse_args().git_index)
