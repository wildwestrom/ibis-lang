#!/usr/bin/env python3
"""Deterministic session-start context digest for the Ibis Lean port.

Replaces the ritual `jj st` / `git log` / find-the-lean-files / grep-for-sorry /
read-the-proof-docs opening that every fresh context window otherwise pays an
LLM to rediscover. Everything here is cheap and local: no `lake build`, no
network, no model.

    python3 .claude/context-digest.py            # human-readable
    python3 .claude/context-digest.py --json     # SessionStart hook envelope

Exits 0 even on internal failure; a broken digest must never break a session.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SKIP_DIRS = {".lake", ".direnv", ".git", ".jj", "dist-newstyle", ".claude", "paper"}

# Proof escape hatches, in the order we want them reported.
ESCAPES = ("sorry", "admit", "axiom", "native_decide", "#exit")

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)


def sh(*args: str) -> str:
    """Run a command, returning stripped stdout ('' on any failure)."""
    try:
        out = subprocess.run(
            args, cwd=ROOT, capture_output=True, text=True, timeout=15
        )
        return out.stdout.strip()
    except Exception:
        return ""


def lean_files(subdir: str | None = None) -> list[Path]:
    """Project .lean files, pruning SKIP_DIRS as we walk.

    Pruning matters: `.lake/` holds the whole of mathlib, so a naive
    `rglob("*.lean")` traverses thousands of irrelevant files before filtering
    them out. `subdir` restricts the walk further still.
    """
    base = ROOT / subdir if subdir else ROOT
    if not base.is_dir():
        return []
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        found.extend(
            Path(dirpath) / f for f in filenames if f.endswith(".lean")
        )
    return sorted(found)


def code_of(line: str) -> str:
    """Live code on a Lean line: string literals blanked, `--` comment dropped.

    Strings go first so a `"a--b"` literal cannot fake a comment, and so Ibis's
    own `"sorry"` / `"admit"` keyword tables in Ibis/Parser.lean are not
    mistaken for Lean escape hatches.
    """
    line = re.sub(r'"(?:[^"\\]|\\.)*"', '""', line)
    return line.split("--", 1)[0]


def strip_block_comments(text: str) -> str:
    return re.sub(r"/-.*?-/", "", text, flags=re.S)


def scan(path: Path) -> dict:
    """Line count, declaration names, and escape-hatch hits for one file."""
    try:
        raw = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return {"lines": 0, "decls": [], "escapes": []}

    body = strip_block_comments(raw)
    decls, escapes = [], []

    for lineno, line in enumerate(body.splitlines(), start=1):
        m = DECL_RE.match(line)
        if m:
            decls.append((m.group(1), m.group(2)))
        code = code_of(line)
        for kw in ESCAPES:
            if not re.search(rf"(?<![\w.]){re.escape(kw)}(?![\w'])", code):
                continue
            # `| admit` heading an inductive/match alternative declares a
            # constructor (Ibis's own Tactic type does this) — a real escape
            # hatch always sits after `=>`, `by`, or on its own.
            if re.match(rf"^\s*\|\s*{re.escape(kw)}\b", code):
                continue
            escapes.append((kw, lineno, line.strip()[:90]))

    return {"lines": len(raw.splitlines()), "decls": decls, "escapes": escapes}


def rel(p: Path) -> str:
    return str(p.relative_to(ROOT))


def age(path: Path) -> str:
    try:
        delta = time.time() - path.stat().st_mtime
    except OSError:
        return "?"
    for unit, size in (("d", 86400), ("h", 3600), ("m", 60)):
        if delta >= size:
            return f"{int(delta // size)}{unit}"
    return "just now"


def newest_mtime(paths) -> float:
    stamps = []
    for p in paths:
        try:
            stamps.append(p.stat().st_mtime)
        except OSError:
            pass
    return max(stamps, default=0.0)


def build_digest() -> str:
    out: list[str] = []
    add = out.append

    files = lean_files()
    scans = {p: scan(p) for p in files}

    # --- toolchain -----------------------------------------------------------
    toolchain = (ROOT / "lean-toolchain").read_text().strip() if (
        ROOT / "lean-toolchain"
    ).exists() else "?"
    lakefile = (ROOT / "lakefile.toml").read_text() if (
        ROOT / "lakefile.toml"
    ).exists() else ""
    mathlib = re.search(r'name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"', lakefile, re.S)
    targets = re.search(r"defaultTargets\s*=\s*\[([^\]]*)\]", lakefile)

    add("## Toolchain")
    add(f"- lean: `{toolchain}`  mathlib rev: `{mathlib.group(1) if mathlib else '?'}`")
    if targets:
        add(f"- lake defaultTargets: {targets.group(1).strip()}")
    add("- build: `timeout 590 lake build IbisProofs` | test: `timeout 590 lake exe ibisTests`")

    # --- vcs -----------------------------------------------------------------
    add("")
    add("## Working copy (jj — do NOT use git to mutate)")
    desc = sh("jj", "log", "-r", "@", "--no-graph", "-T",
              r'change_id.short() ++ " " ++ coalesce(description.first_line(), "(no description)")')
    add(f"- `@` = {desc or '?'}")
    stat = sh("jj", "diff", "--stat")
    add(f"- diff vs parent: {stat.splitlines()[-1] if stat else 'clean'}")
    for line in (sh("jj", "bookmark", "list") or "").splitlines()[:4]:
        add(f"- bookmark {line.strip()}")
    recent = sh("jj", "log", "-r", "ancestors(@, 6)", "--no-graph", "-T",
                r'coalesce(description.first_line(), "(wc)") ++ "\n"')
    if recent:
        add("- recent: " + " | ".join(l for l in recent.splitlines() if l.strip())[:400])

    # --- escapes -------------------------------------------------------------
    add("")
    add("## Proof escape hatches (regex scan, comments stripped)")
    hits = [
        (rel(p), kw, ln, txt)
        for p, s in scans.items()
        for (kw, ln, txt) in s["escapes"]
    ]
    if not hits:
        add(f"- none across {len(files)} .lean files: no `sorry`/`admit`/`axiom`/`native_decide`")
    else:
        counts: dict[str, int] = {}
        for _, kw, _, _ in hits:
            counts[kw] = counts.get(kw, 0) + 1
        add("- totals: " + ", ".join(f"`{k}`×{v}" for k, v in sorted(counts.items())))
        for f, kw, ln, txt in hits[:25]:
            add(f"  - {f}:{ln} [{kw}] {txt}")
        if len(hits) > 25:
            add(f"  - … {len(hits) - 25} more")

    # --- inventories ---------------------------------------------------------
    for title, pred in (
        ("Proof library (IbisProofs, mathlib-backed)",
         lambda p: rel(p).startswith("IbisProofs")),
        ("Runtime (Ibis)", lambda p: rel(p).startswith("Ibis/") or rel(p) == "Ibis.lean"),
        ("Top level", lambda p: "/" not in rel(p) and not rel(p).startswith("Ibis")),
    ):
        group = [p for p in files if pred(p)]
        if not group:
            continue
        add("")
        add(f"## {title}")
        for p in group:
            s = scans[p]
            thms = [n for k, n in s["decls"] if k in ("theorem", "lemma")]
            defs = [n for k, n in s["decls"] if k not in ("theorem", "lemma")]
            head = f"- `{rel(p)}` {s['lines']}L"
            if thms:
                head += f", {len(thms)} thm"
            if defs:
                head += f", {len(defs)} def"
            add(head)
            if thms:
                add(f"    thm: {', '.join(thms[:18])}"
                    + (f" … +{len(thms) - 18}" if len(thms) > 18 else ""))
            if defs:
                add(f"    def: {', '.join(defs[:14])}"
                    + (f" … +{len(defs) - 14}" if len(defs) > 14 else ""))

    # --- docs ----------------------------------------------------------------
    add("")
    add("## Docs (read on demand — not preloaded)")
    for md in sorted(ROOT.glob("*.md")):
        n = len(md.read_text(encoding="utf-8", errors="replace").splitlines())
        add(f"- `{md.name}` {n}L, touched {age(md)} ago")

    # --- build freshness -----------------------------------------------------
    # Only our own artifacts under .lake/build — mathlib's ~8.7k oleans in
    # .lake/packages carry download mtimes that say nothing about our build.
    src = newest_mtime(files)
    build_dir = ROOT / ".lake" / "build"
    olean = newest_mtime(build_dir.rglob("*.olean")) if build_dir.is_dir() else 0.0
    add("")
    if olean == 0.0:
        add("## Build state: no artifacts in `.lake/build` — next build is a cold one")
    elif src > olean:
        add("## Build state: STALE — .lean sources are newer than the newest .olean")
    else:
        add("## Build state: artifacts newer than sources (last build looks current)")

    return "\n".join(out)


def check_proofs() -> list[tuple[str, str, int, str]]:
    """Escape-hatch hits under `IbisProofs/` only.

    Runtime modules are deliberately out of scope: Ibis/Syntax.lean and
    Ibis/Parser.lean carry Ibis's own `sorry`/`admit` source-language tokens,
    which are not Lean escape hatches. Only the proof library makes the
    no-`sorry` promise that PROOFS.md advertises.
    """
    targets = lean_files("IbisProofs") + [ROOT / "IbisProofs.lean"]
    return [
        (rel(p), kw, ln, txt)
        for p in targets
        if p.exists()
        for (kw, ln, txt) in scan(p)["escapes"]
    ]


def guard_proofs() -> int:
    """UserPromptSubmit guard. Silent unless the proof library regressed."""
    try:
        hits = check_proofs()
    except Exception:
        return 0  # a spurious alarm on every prompt is worse than no alarm

    if not hits:
        return 0  # the common case: emit nothing at all

    listed = "\n".join(f"- {f}:{ln} [{kw}] {txt}" for f, kw, ln, txt in hits[:12])
    if len(hits) > 12:
        listed += f"\n- … {len(hits) - 12} more"
    plural = "" if len(hits) == 1 else "es"

    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "UserPromptSubmit",
            "additionalContext": (
                f"## Proof-hygiene regression: {len(hits)} escape hatch{plural} "
                "in IbisProofs/\n\n" + listed + "\n\n"
                "PROOFS.md claims the proof sources contain no `sorry`, new axioms, "
                "or `native_decide`. That claim is now false. Either close the goal, "
                "remove the theorem, or narrow the claim in PROOFS.md — do not leave "
                "a stub and describe the result as proved."
            ),
        },
        "systemMessage": (
            f"⚠ IbisProofs/ contains {len(hits)} proof escape hatch{plural} "
            f"({', '.join(sorted({kw for _, kw, _, _ in hits}))})"
        ),
    }))
    return 0


def main() -> int:
    if "--check-proofs" in sys.argv:
        return guard_proofs()

    try:
        digest = build_digest()
    except Exception as exc:  # never break a session over a digest
        digest = f"context-digest failed: {type(exc).__name__}: {exc}"

    if "--json" in sys.argv:
        print(json.dumps({
            "hookSpecificOutput": {
                "hookEventName": "SessionStart",
                "additionalContext": (
                    "# Auto-loaded project digest (.claude/context-digest.py)\n"
                    "Generated deterministically at session start. Trust these numbers "
                    "over re-deriving them; re-run the script if you change files.\n\n"
                    + digest
                ),
            },
            "suppressOutput": True,
        }))
    else:
        print(digest)
    return 0


if __name__ == "__main__":
    sys.exit(main())
