#!/usr/bin/env python3
"""Point the web blueprint's links to declarations of this library at their source.

leanblueprint links every Lean declaration to Mathlib's documentation. This rewrites the links
in `blueprint/web/*.html` to declarations of the `Coarse` library into `vscode://file/` links
that open the source at the declaration; links to other declarations are left as they are.
Run after `leanblueprint web`, which writes the names to `blueprint/lean_decls`.
"""

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WEB = ROOT / "blueprint" / "web"
DECLS = ROOT / "blueprint" / "lean_decls"
LINK = re.compile(r'href="https://leanprover-community\.github\.io/mathlib4_docs/find/#doc/([^"]+)"')


def locations():
    """Map each declaration of this library named in `lean_decls` to its file and line."""
    out = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/DeclLocations.lean"],
        cwd=ROOT, input=DECLS.read_text(), capture_output=True, text=True, check=True).stdout
    locs = {}
    for row in out.splitlines():
        name, module, line = row.split("\t")
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if module.split(".")[0] == "Coarse" and path.exists():
            locs[name] = (path, line)
    return locs


def main():
    locs = locations()
    def link(m):
        if m.group(1) not in locs:
            return m.group(0)
        path, line = locs[m.group(1)]
        return f'href="vscode://file{path}:{line}"'
    for page in WEB.glob("*.html"):
        text = page.read_text()
        new = LINK.sub(link, text)
        if new != text:
            page.write_text(new)
    print(f"Linked {len(locs)} declarations to their source.")


if __name__ == "__main__":
    main()
