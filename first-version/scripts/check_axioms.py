#!/usr/bin/env python3
"""Check the axiom reports of the eleven theorems of EinsteinRelation/MainTheorems.lean.

The script writes a temporary Lean file that imports the library and asks for the axiom
report of each theorem, runs it with `lake env lean`, and requires each report to consist of
exactly `propext`, `Classical.choice` and `Quot.sound`. It fails on `sorryAx`, on any other
axiom, on a warning or error, and on a missing, unexpected or duplicate report.

Usage (from the repository root, after `lake build`):
    python3 scripts/check_axioms.py            # generate, run and check
    python3 scripts/check_axioms.py --log FILE # also keep the Lean output in FILE
"""
import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

THEOREMS = [
    'EinsteinRelation.mobility_rate',
    'EinsteinRelation.regeneration_renewal',
    'EinsteinRelation.regeneration_occupation',
    'EinsteinRelation.entropy_fisher_bound',
    'EinsteinRelation.entropy_divergence_bound',
    'EinsteinRelation.entropy_resolvent_bound',
    'EinsteinRelation.corrector_moments',
    'EinsteinRelation.corrector_conditional',
    'EinsteinRelation.corrector_local',
    'EinsteinRelation.scalar_decomposition',
    'EinsteinRelation.mobility_rate_sharp',
]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
COMMAND = '#print axioms'


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--log', type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent.parent
    source = 'import EinsteinRelation\n\n' + ''.join(f'{COMMAND} {t}\n' for t in THEOREMS)
    with tempfile.TemporaryDirectory(prefix='einstein-axioms-') as tmp:
        path = pathlib.Path(tmp) / 'AxiomsAudit.lean'
        path.write_text(source)
        run = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root,
                             capture_output=True, text=True)
    log = run.stdout + run.stderr
    if args.log:
        args.log.write_text(log)
    print(log, end='')
    if run.returncode != 0:
        print('lake env lean failed with exit code', run.returncode, file=sys.stderr)
        return 1
    if re.search(r'warning:|error:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
        print('The axiom audit emitted a warning or an error, or reported sorryAx.', file=sys.stderr)
        return 1
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    seen = set()
    for theorem, axioms in reports:
        if theorem not in THEOREMS or theorem in seen:
            print('Unexpected or duplicate axiom report: ' + theorem, file=sys.stderr)
            return 1
        actual = [a.strip() for a in axioms.split(',')]
        if len(actual) != 3 or set(actual) != STANDARD:
            print(f'Unexpected axioms for {theorem}: {axioms}', file=sys.stderr)
            return 1
        seen.add(theorem)
    missing = [t for t in THEOREMS if t not in seen]
    if missing:
        print('Missing axiom reports: ' + ', '.join(missing), file=sys.stderr)
        return 1
    print(f'All {len(THEOREMS)} theorems use exactly propext, Classical.choice and Quot.sound.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
