#!/usr/bin/env python3
"""Require one axiom report for each of the twenty-one numbered results, listing the three standard axioms and
otherwise only the literature inputs of the README. Usage: check_axioms.py <log of EinsteinFullAudit/Axioms.lean>"""
import pathlib
import re
import sys

expected = {
    'EinsteinFull.Frozen.uniform_small_force_expansion', 'EinsteinFull.Frozen.mobility_rate',
    'EinsteinFull.Frozen.response', 'EinsteinFull.Frozen.environmental_factorization',
    'EinsteinFull.Frozen.uniform_lattice_renewal', 'EinsteinFull.Frozen.local_mixing',
    'EinsteinFull.Frozen.correlation_tail', 'EinsteinFull.Frozen.gauge', 'EinsteinFull.Frozen.forced_scalar_decay',
    'EinsteinFull.Frozen.forced_local_estimates', 'EinsteinFull.Frozen.forced_weak_flux',
    'EinsteinFull.Frozen.covariance_scaling', 'EinsteinFull.Frozen.forced_comparison',
    'EinsteinFull.Frozen.late_force_replacement', 'EinsteinFull.Frozen.finite_time_unforced_commutator',
    'EinsteinFull.Frozen.late_homogeneous_propagation', 'EinsteinFull.Frozen.endpoint_comparison',
    'EinsteinFull.Frozen.correlation_profile', 'EinsteinFull.Frozen.kernel_integration',
    'EinsteinFull.Frozen.sharp_example', 'EinsteinFull.Frozen.regeneration_factorization',
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}
# The literature inputs of the README, each stated in EinsteinFull/External/ or in
# EinsteinFull/Frozen/GantertRegenerationTail.lean; the comparator runner reads the same list.
root = pathlib.Path(__file__).resolve().parents[1]
literature = {'EinsteinFull.External.' + n for n in (root / 'scripts/literature_inputs.txt').read_text().split()}
log = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'warning:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
    raise SystemExit('Axiom audit emitted a warning or reported sorryAx')
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
seen, used = set(), set()
for theorem, axioms in reports:
    if theorem not in expected or theorem in seen:
        raise SystemExit('Unexpected or duplicate axiom report: ' + theorem)
    actual = {a.strip() for a in axioms.split(',')}
    if not standard <= actual or not actual <= standard | literature:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + ', '.join(sorted(actual - standard - literature)))
    seen.add(theorem); used |= actual - standard
if seen != expected:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(expected - seen)))
print(f'All {len(expected)} numbered results use exactly propext, Classical.choice, Quot.sound and literature '
      f'inputs ({len(used)} of the {len(literature)} listed).')
