#!/usr/bin/env python3
"""Point the web blueprint's links to declarations of this library at their source.

leanblueprint links every Lean declaration to Mathlib's documentation. This rewrites the links
in `blueprint/web/*.html` to declarations of the `Coarse` library into `vscode://file/` links
that open the source at the declaration; links to other declarations are left as they are.
With `--source URL`, the links point at `URL/<path>#L<line>` instead, for the published blueprint.
The locations are read from the `.ilean` files of the last `lake build`.
Run after `leanblueprint web`.
"""

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WEB = ROOT / "blueprint" / "web"
ILEAN = ROOT / ".lake" / "build" / "lib" / "lean" / "Coarse"
LINK = re.compile(r'href="https://leanprover-community\.github\.io/mathlib4_docs/find/#doc/([^"]+)"')


def locations():
    """Map each declaration of this library to the file and line of its name."""
    locs = {}
    for ilean in ILEAN.rglob("*.ilean"):
        for key, ref in json.loads(ilean.read_text())["references"].items():
            const = json.loads(key).get("c")
            if const is None or not ref.get("definition"):
                continue
            path = ROOT.joinpath(*const["m"].split(".")).with_suffix(".lean")
            if path.exists():
                locs[const["n"]] = (path, ref["definition"][0] + 1)
    return locs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", help="URL of the repository tree, such as "
                        "https://github.com/OWNER/REPO/blob/COMMIT")
    source = parser.parse_args().source
    locs = locations()
    linked = set()
    def link(m):
        if m.group(1) not in locs:
            return m.group(0)
        linked.add(m.group(1))
        path, line = locs[m.group(1)]
        if source:
            return f'href="{source}/{path.relative_to(ROOT).as_posix()}#L{line}"'
        return f'href="vscode://file{path}:{line}"'
    for page in WEB.glob("*.html"):
        text = page.read_text()
        new = LINK.sub(link, text)
        if new != text:
            page.write_text(new)
    print(f"Linked {len(linked)} declarations to their source.")


if __name__ == "__main__":
    main()
