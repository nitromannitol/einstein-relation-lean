#!/usr/bin/env bash
# Run every comparator pair under EinsteinRelationAudit/. A missing pair or a failed check is fatal.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
case "${1:-}" in
  '') ;;
  --help) cat <<'USAGE'
Usage: scripts/run_comparators.sh

Runs leanprover/comparator on every pair EinsteinRelationAudit/<Pair>/comparator.json.
Set COMPARATOR_BIN, COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT and COMPARATOR_NANODA to the
paths of the comparator, landrun, lean4export (built for the toolchain in lean-toolchain) and
nanoda_bin executables; the defaults are the paths used by .github/workflows/comparator.yml.
The library is built first; the audit modules are then compiled in a fresh copy of the
checkout that reuses the library and dependency builds. Logs are written under
.lake/comparator-logs/.
USAGE
    exit 0 ;;
  *) echo "Unknown option: $1" >&2; exit 2 ;;
esac
for command_name in lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 1; }
done
log_dir="$repository_root/.lake/comparator-logs"
mkdir -p "$log_dir"
config_dir=$(mktemp -d "${TMPDIR:-/tmp}/einstein-comparators.XXXXXXXX")
trap 'rm -rf "$config_dir"' EXIT

# Validate the configurations and write protected copies; the required pairs must exist.
python3 - "$repository_root" "$config_dir" <<'PY'
import json
import pathlib
import re
import sys

root, destination = map(pathlib.Path, sys.argv[1:])
audit = root / 'EinsteinRelationAudit'
required = {'MobilityRate', 'SharpExample'}
paths = sorted(audit.rglob('comparator.json'))
missing = required - {p.parent.name for p in paths}
if missing:
    raise SystemExit('Missing required comparator pairs: ' + ', '.join(sorted(missing)))
allowed_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms',
                'definition_names', 'enable_nanoda'}
standard_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
def unique_keys(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('Duplicate configuration key: ' + key)
        result[key] = value
    return result
manifest = []
for index, path in enumerate(paths):
    config = json.loads(path.read_text(), object_pairs_hook=unique_keys)
    if not isinstance(config, dict) or set(config) - allowed_keys:
        raise SystemExit(f'{path}: unsupported configuration fields')
    axioms = config.get('permitted_axioms')
    if not isinstance(axioms, list) or len(axioms) != 3 or set(axioms) != standard_axioms:
        raise SystemExit(f'{path}: permitted_axioms must be exactly the three standard axioms')
    names = config.get('theorem_names')
    if not isinstance(names, list) or not names or any(not isinstance(n, str) or not n.strip() for n in names):
        raise SystemExit(f'{path}: theorem_names must be a nonempty list of declaration names')
    for key in ['challenge_module', 'solution_module']:
        module = config.get(key)
        if not isinstance(module, str) or not re.fullmatch(r'EinsteinRelationAudit(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module):
            raise SystemExit(f'{path}: invalid {key}')
        if not root.joinpath(*module.split('.')).with_suffix('.lean').is_file():
            raise SystemExit(f'{path}: missing {key} source')
    # The NanoDa replay is never disabled.
    config['enable_nanoda'] = True
    output = destination / f'{index:03d}.json'
    output.write_text(json.dumps(config, indent=2) + '\n')
    manifest.append(f'{index:03d}\t{path.relative_to(root)}\t{output}')
(destination / 'pairs.tsv').write_text('\n'.join(manifest) + '\n')
print(f'Validated {len(paths)} comparator pairs.')
PY

: "${COMPARATOR_BIN:=$HOME/tools/comparator/.lake/build/bin/comparator}"
: "${COMPARATOR_LANDRUN:=$HOME/tools/bin/landrun}"
: "${COMPARATOR_LEAN4EXPORT:=$HOME/tools/lean4export/.lake/build/bin/lean4export}"
: "${COMPARATOR_NANODA:=$HOME/tools/nanoda_lib/target/release/nanoda_bin}"
export COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA
for tool_path in "$COMPARATOR_BIN" "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA"; do
  [ -x "$tool_path" ] || { echo "Missing executable: $tool_path" >&2; exit 1; }
done
# A denied write alone is insufficient: also check that the sandbox can execute.
probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/einstein-landrun.XXXXXXXX")
probe="$probe_dir/escape"
if ! "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec -- /bin/true; then
  rm -rf "$probe_dir"
  echo 'landrun could not execute the permitted sandbox probe' >&2
  exit 1
fi
"$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec \
  -- /bin/sh -c 'printf escaped > "$1"' sh "$probe" || true
if [ -e "$probe" ]; then
  rm -rf "$probe_dir"
  echo 'landrun allowed an out-of-sandbox write' >&2
  exit 1
fi
rm -rf "$probe_dir"

lake build EinsteinRelation 2>&1 | tee "$log_dir/library-build.log"

# A fresh copy of the checkout gives the audit modules empty build paths while reusing the
# library and dependency builds. The copy is kept under .lake/comparator-runs/.
run_parent="$repository_root/.lake/comparator-runs"
mkdir -p "$run_parent"
run_root=$(mktemp -d "$run_parent/run.XXXXXXXX")
python3 - "$repository_root" "$run_root" <<'PY'
import pathlib
import shutil
import sys

source, destination = map(pathlib.Path, sys.argv[1:])
shutil.copytree(source, destination, dirs_exist_ok=True, symlinks=True,
                ignore=shutil.ignore_patterns('.lake', '.git'))
local_lake = destination / '.lake'
local_lake.mkdir()
packages = source / '.lake/packages'
if packages.is_dir():
    shutil.copytree(packages, local_lake / 'packages', symlinks=True,
                    ignore=shutil.ignore_patterns('*.setup.json'))
build = source / '.lake/build'
if build.is_dir():
    for path in build.rglob('*'):
        relative = path.relative_to(build)
        if any(part == 'EinsteinRelationAudit' or part.startswith('EinsteinRelationAudit.')
               for part in relative.parts):
            continue
        output = local_lake / 'build' / relative
        if path.is_dir():
            output.mkdir(parents=True, exist_ok=True)
        elif path.is_file() and not path.name.endswith('.setup.json'):
            output.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, output)
print('Fresh audit checkout: ' + str(destination))
PY
printf '%s\n' "$run_root" | tee "$log_dir/audit-checkout.txt"
cd "$run_root"
unset LEAN_PATH
lake build EinsteinRelationAudit 2>&1 | tee "$log_dir/audit-build.log"

failed=0
checked=0
while IFS=$'\t' read -r index source_config protected_config; do
  printf '\nChecking %s\n' "$source_config"
  log="$log_dir/$index.log"
  if lake env "$COMPARATOR_BIN" "$protected_config" 2>&1 | tee "$log"; then
    result=0
  else
    result=1
  fi
  if [ "$result" -eq 0 ] && grep -Fxq 'Your solution is okay!' "$log"; then
    printf '%s: OK\n' "$source_config"
  else
    printf '%s: FAILED\n' "$source_config" >&2
    failed=1
  fi
  checked=$((checked + 1))
done < "$config_dir/pairs.tsv"
[ "$checked" -ge 2 ] || { echo 'Fewer than two comparator pairs ran' >&2; exit 1; }
[ "$failed" -eq 0 ] || exit 1
printf '\nAll %s comparator pairs passed. Logs: %s\n' "$checked" "$log_dir"
