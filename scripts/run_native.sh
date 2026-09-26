#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 || "$1" != /* || "$2" != /* || ! -x "$1" ]]; then
  printf 'usage: scripts/run_native.sh /absolute/doc-gen4 /absolute/output-dir\n' >&2
  exit 2
fi

tool=$1
work=$2
revision=a9f1a38787d33205c469ff89710563fffb4974fd
mkdir -p "$work/analysis" "$work/rendered" "$work/receipts"
printf '%s\n' "source_revision=$revision" \
  'docgen_revision=97d4ecdfc8e09e7f511724c25e303d448de6a3db' \
  "docgen_executable=$tool" "started=$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  "cgroup_memory_max=$(cat /sys/fs/cgroup/memory.max)" \
  > "$work/receipts/context.txt"
cat /sys/fs/cgroup/memory.events > "$work/receipts/memory-events-before.txt"
while read -r module path; do
  source_uri="https://github.com/FormalFrontier/sheaf-cohomology/blob/$revision/$path"
  printf '%s\t%s\t%s\n' "$module" "$path" "$source_uri" >> "$work/receipts/source-uris.tsv"
  (time lake env "$tool" single --build "$work/analysis" \
    "$module" api.db "$source_uri" \
    > "$work/receipts/single-$module.stdout" \
    2> "$work/receipts/single-$module.stderr") \
    2> "$work/receipts/single-$module.time"
done < <(python3 -c 'import sys;sys.path.insert(0,"scripts");import generate_api as api;[print(m,p) for m,p in api.MODULE_PATHS.items()]')
(time lake env "$tool" bibPrepass --build "$work/rendered" --none \
  > "$work/receipts/bib.stdout" 2> "$work/receipts/bib.stderr") \
  2> "$work/receipts/bib.time"
(time lake env "$tool" fromDb --build "$work/rendered" \
  --manifest "$work/rendered/manifest.json" "$work/analysis/api.db" \
  > "$work/receipts/from-db.stdout" 2> "$work/receipts/from-db.stderr") \
  2> "$work/receipts/from-db.time"
cat /sys/fs/cgroup/memory.events > "$work/receipts/memory-events-after.txt"
cat /sys/fs/cgroup/memory.peak > "$work/receipts/cgroup-memory-peak.txt"
printf 'completed=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  >> "$work/receipts/context.txt"
