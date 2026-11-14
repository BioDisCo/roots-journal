#!/usr/bin/env python3
"""Check local Lean imports and the manuscript's source-file/line links."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
DECLARATION = re.compile(r"\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma)\s+(\S+)")


def check_sources():
    errors = []
    sources = [LEAN / "AsymptoticSubspace.lean"]
    sources.extend(sorted((LEAN / "AsymptoticSubspace").rglob("*.lean")))
    required = set(sources)
    for source in sources:
        if not source.is_file():
            errors.append(f"Missing source: {source.relative_to(ROOT)}")
            continue
        for module in re.findall(r"^(?:public\s+)?import\s+(AsymptoticSubspace(?:\.\w+)*)", source.read_text(), re.M):
            dependency = LEAN / (module.replace(".", "/") + ".lean")
            required.add(dependency)
            if not dependency.is_file():
                errors.append(f"{source.relative_to(ROOT)} imports missing source {module}")

    # Source archives need no Git metadata; a working checkout also checks that
    # required sources will be included in its next commit.
    if (ROOT / ".git").exists():
        tracked = set(subprocess.check_output(
            ["git", "-C", str(ROOT), "ls-files", "-z"], text=True
        ).split("\0"))
        for source in sorted(required):
            relative = str(source.relative_to(ROOT))
            if relative not in tracked:
                errors.append(f"Required Lean source is not tracked by Git: {relative}")
    return errors, len(sources)


def check_badges():
    errors = []
    manuscript = (ROOT / "manuscript/main.tex").read_text()
    targets = re.findall(r"\\leanurl\{([^{}]+)\}", manuscript)
    for target in targets:
        filename, _, anchor = target.replace(r"\#", "#").partition("#")
        source = LEAN / "AsymptoticSubspace" / filename
        if not source.is_file():
            errors.append(f"Badge points to missing source: {target}")
            continue
        if not anchor:
            continue
        match = re.fullmatch(r"L(\d+)-L(\d+)", anchor)
        if match is None:
            errors.append(f"Unrecognized badge line range: {target}")
            continue
        start, end = map(int, match.groups())
        lines = source.read_text().splitlines()
        if not 1 <= start <= end <= len(lines):
            errors.append(f"Badge line range is outside its source: {target}")
        elif not DECLARATION.match(lines[start - 1]):
            errors.append(f"Badge line range does not start at a declaration: {target}")
    if not targets:
        errors.append("No Lean badge targets found in manuscript/main.tex")
    return errors, len(targets)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources-only", action="store_true")
    args = parser.parse_args()
    errors, count = check_sources()
    if not errors:
        print(f"Checked {count} Lean source files and their local imports.")
    if not args.sources_only:
        badge_errors, badges = check_badges()
        errors.extend(badge_errors)
        if not badge_errors:
            print(f"Checked {badges} manuscript badge targets and their declaration anchors.")
    for error in errors:
        print(error, file=sys.stderr)
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
