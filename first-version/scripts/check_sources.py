#!/usr/bin/env python3
"""Source audit of the Lean files.

* The library (`EinsteinRelation.lean` and `EinsteinRelation/`) and the comparator solutions
  must not contain, outside comments and string literals, any of the tokens `sorry`, `admit`,
  `native_decide`, `implemented_by`, an `axiom` declaration, or a `#print`/`#eval`/`#exit`
  command.
* Each comparator challenge (`EinsteinRelationAudit/<Pair>/Challenge.lean` with its
  `Vocabulary/` files) must import only Mathlib and vocabulary files of the same pair; the
  challenge file contains exactly one `sorry`, and the vocabulary files none; no other
  forbidden token occurs.

Usage: python3 scripts/check_sources.py   (from any directory)
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FORBIDDEN = [
    (re.compile(r'(?<![\w.])sorry(?![\w])'), 'sorry'),
    (re.compile(r'(?<![\w.])admit(?![\w])'), 'admit'),
    (re.compile(r'(?<![\w.])native_decide(?![\w])'), 'native_decide'),
    (re.compile(r'(?<![\w.])implemented_by(?![\w])'), 'implemented_by'),
    (re.compile(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\s'), 'axiom'),
    (re.compile(r'#(?:print|eval|exit|check|reduce)\b'), 'debug command'),
]


def code_only(text: str) -> str:
    """Remove comments (nested block comments and line comments) and string literals."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if text.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if text[i] == '\n':
                out.append('\n')
            i += 1
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append('""')
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return ''.join(out)


def findings(path: pathlib.Path):
    code = code_only(path.read_text())
    hits = []
    for rx, name in FORBIDDEN:
        for m in rx.finditer(code):
            line = code.count('\n', 0, m.start()) + 1
            hits.append((name, line))
    return hits


def main() -> int:
    bad = 0
    library = [ROOT / 'EinsteinRelation.lean'] + sorted((ROOT / 'EinsteinRelation').rglob('*.lean'))
    audit = sorted((ROOT / 'EinsteinRelationAudit').rglob('*.lean')) if (ROOT / 'EinsteinRelationAudit').is_dir() else []
    for path in library + [p for p in audit if p.name != 'Challenge.lean' and 'Vocabulary' not in p.parts]:
        for name, line in findings(path):
            print(f'{path.relative_to(ROOT)}:{line}: forbidden {name}')
            bad += 1
    challenges = [p for p in audit if p.name == 'Challenge.lean']
    for path in challenges:
        pair = path.parent.name
        files = [path] + sorted((path.parent / 'Vocabulary').rglob('*.lean'))
        for f in files:
            hits = findings(f)
            sorries = [h for h in hits if h[0] == 'sorry']
            others = [h for h in hits if h[0] != 'sorry']
            expected = 1 if f == path else 0
            if len(sorries) != expected:
                print(f'{f.relative_to(ROOT)}: expected {expected} sorry, found {len(sorries)}')
                bad += 1
            for name, line in others:
                print(f'{f.relative_to(ROOT)}:{line}: forbidden {name}')
                bad += 1
            for m in re.finditer(r'(?m)^\s*(?:public\s+)?import\s+(\S+)', f.read_text()):
                mod = m.group(1)
                if not (mod == 'Mathlib' or mod.startswith('Mathlib.')
                        or mod.startswith(f'EinsteinRelationAudit.{pair}.Vocabulary.')):
                    print(f'{f.relative_to(ROOT)}: imports {mod}, which is neither Mathlib nor vocabulary')
                    bad += 1
    print(f'Checked {len(library)} library files, {len(audit)} audit files '
          f'({len(challenges)} challenges): {bad} problem(s).')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
