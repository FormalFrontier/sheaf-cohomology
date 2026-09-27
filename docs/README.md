# Historical native API generation and verification

[API.md](API.md) renders the **original** 26 Lean modules (24 unchanged subjects,
the original aggregate and private-example client) from doc-gen4's **native**
per-module
JSON and HTML: 556 display sites (545 HTML top-level declarations and 11
nested constructors/structure/class fields). All 11 nested sites also occur
as native JSON rows; the two presentations are cross-checked, not counted
twice. There are 399 native source docstrings and 157 sites without one; a
missing docstring is labeled instead of invented. The fixed
inventory `scripts/api_inventory.json` binds every site to its module,
name, kind, visible signature and, for top-level declarations, native
docstring. `api-manifest.json` binds source/pin bytes, the native input record
and HTML hashes and the resulting Markdown **for the old analyzed revision**.
In particular, the unchanged manifest's `api_sha256` is the hash of the
original generated `docs/API.md` in the pre-transfer accepted tree, not this
file's editorially updated introduction. The historical generated file can
be checked in that old revision; do not relabel the old hash as a new current
Markdown attestation.
The current 61 Lean modules also include eighteen new subjects and seventeen private
client leaves, covered by [AbelianForget.md](AbelianForget.md),
[SquareTransition.md](SquareTransition.md) and
[SheafedSpace.md](SheafedSpace.md) and
[ConePullbackCocone.md](ConePullbackCocone.md) and
[AbelianForgetConePullbackCocone.md](AbelianForgetConePullbackCocone.md) and
[DiagramPushforward.md](DiagramPushforward.md) and
[AbelianForgetDiagramPushforward.md](AbelianForgetDiagramPushforward.md) and
[ConeOfPullbackCocone.md](ConeOfPullbackCocone.md) and
[ConePullbackLimit.md](ConePullbackLimit.md) and
[SheafedSpaceLimitConstruction.md](SheafedSpaceLimitConstruction.md) and
[SheafedSpaceLimitPreservation.md](SheafedSpaceLimitPreservation.md) and
[AbelianSheafedSpaceCofilteredLimits.md](AbelianSheafedSpaceCofilteredLimits.md) and
[SheafedSpaceConePullbackLimitConverse.md](SheafedSpaceConePullbackLimitConverse.md), not by this
native batch. The old root and example-client source hashes do not match the
current changed roots. Reproducing these historical records is
distinct from accepting their mathematical meaning or auditing kernel proofs.
For the 157 missing-docstring sites, the shipped text is a generic pointer to
the source and module guide, not an independently authored per-site explanation.
Its adequacy for the whole public API is assessed in semantic review.

The manifest fields `proof_certification: false` and `release_acceptance: false`
describe the documentation generator's scope: it certifies neither proofs nor
release acceptance. They are not the lifecycle status of the library or a
negative result of a build or axiom audit. Actual release decisions are made
separately for exact revisions using the applicable build, complete standard-axiom
audit and independent lightweight assessment described in the project README.

Displayed signatures retain all native visible binder tokens and declaration
modifiers; only whitespace is normalized. Native pretty-printing may omit
inferable types or require its surrounding namespace, so displayed fragments
need not elaborate standalone. The exact Lean source and actual universes are
authoritative. Private Lean helpers and private named examples are **not**
included as public API rows and require their own proof inventory. A module
with no displayed declarations still participates in the 26-module native
selection; the example client's entries are private by design.

Twelve displayed rows are marked **Source-local instance registration** from
their exact frozen source ranges. These `local instance` registrations do not
install globally available typeclass instances; some native display headers say
`theorem` or `instance` without recording that scope. The annotation changes
neither the native header nor the docstring. Registration scope and declaration
visibility are distinct: this guide makes no claim about explicit-name access.
The fixed adapter checks the twelve source lines/spans against the displayed
names before rendering the annotation.

## Toolchain and separate inputs

Use the library's pinned Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and nine-package
`lake-manifest.json`. Use an **unchanged**, separate doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, including its own
manifest. Its `single` command records each module with an explicit immutable
`sourceUri`; `fromDb` emits both declaration JSON and HTML. Building doc-gen4
itself does not depend on mathlib, and it does not change this library's Lake
pins. Its C dependencies may require Lean's bundled `bin/cc` on `PATH`.

The following **historical reproduction** is for a separate checkout of
pre-transfer tree `3a7204971fbbbb0a130335eda04b9d9d2b157267`, which includes
the frozen adapter and old 26 Lean modules, **not** the changed current
61-module checkout. The `source_revision` below remains the older analyzed
`a9f1a38787d33205c469ff89710563fffb4974fd`, which is in that checkout's
Git history. Use Bash, Python 3, git, elan and Lake. Install the pinned
toolchain, fetch the **matching mathlib cache successfully before the project
build**, and build the old modules and old example target with the default build:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

In the separate fixed doc-gen4 checkout, run `lake build doc-gen4` with its
own `lean-toolchain` and manifest; where necessary, prepend the path to that
installed toolchain's `bin` directory to `PATH` first. Then set its **actual
absolute executable path** and run this in this project's root. The two
checkouts must stay separate:

```sh
docgen_executable=/absolute/path/to/doc-gen4/.lake/build/bin/doc-gen4
docs_work=$(mktemp -d)
mkdir -p "$docs_work/analysis" "$docs_work/rendered"
source_revision=a9f1a38787d33205c469ff89710563fffb4974fd
while read -r module path; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" \
    "$module" api.db \
    "https://github.com/FormalFrontier/sheaf-cohomology/blob/$source_revision/$path"
done < <(python3 -c 'import sys; sys.path.insert(0,"scripts"); import generate_api as api; [print(module, path) for module, path in api.MODULE_PATHS.items()]')
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" \
  --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" \
  --html-root "$docs_work/rendered/doc" --source-revision "$source_revision" --check
SHEAF_NATIVE_DATA="$docs_work/rendered/doc-data" \
SHEAF_HTML_ROOT="$docs_work/rendered/doc" python3 -B scripts/test_generate_api.py
python3 -O -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" \
  --html-root "$docs_work/rendered/doc" --source-revision "$source_revision" --check
```

The native database's parent directory must exist before `single`. The frozen
adapter and its hashes are historical reproduction checks; they do not generate
a new 61-module reference, certify the current roots, or constitute a required
new-generation release gate. For the current checkout, use the lightweight
[AbelianForget](AbelianForget.md) and [SquareTransition](SquareTransition.md)
API supplements, applicable proof/build evidence and
normal link/scope checks instead of inventing a regenerated receipt. Preserve
its manifest, raw JSON and source HTML outside the published library when
performing a review. The adapter refuses missing/extra modules and display
sites, wrong names, kinds, signatures or docstrings, malformed header tags,
changed source ranges, wrong 40-hex URI/path and changed source or pin bytes.
Where the frozen development input `a9f1a38787d33205c469ff89710563fffb4974fd`
is in Git, the adapter checks every shipped Lean and pin file byte-for-byte
against that input. A source-only public lineage without that Git object must
instead reproduce the committed complete source/pin hash manifest;
these hashes validate bytes but do **not** attest that supplied JSON was
genuinely generated by doc-gen4. Review the native-generation command receipt
and raw inputs separately. The full `a9f1a38787d33205c469ff89710563fffb4974fd`
GitHub URIs in the native `sourceUri` records and commands above are historical
generation provenance; they do not assert that the object exists on GitHub.
The frozen source links in API.md are relative to the old subject paths; their
source ranges remain applicable to the unchanged old subjects. The changed root
and example files require separate current-tree link/scope inspection, not a
claim that their old source hashes still match. A future
parentless public history need not regenerate native docs merely because it
lacks that development commit. Renew documentation checks for genuinely changed
inputs without relabeling historical native source hashes as a successor check.
The tree need not embed its own future commit hash to establish this binding.

## Author development baseline

In the worker's four-CPU, 15 GiB cgroup on 2026-09-25, the author reported
1m24s for the matching cache fetch, 16m26s for the unchanged default build
(2,373 Lake jobs), and 1m13s for the separate doc-gen4 build after fixing
the compiler path. The native batch has timestamped start/end records spanning
2m28s; the other three durations have no separate timestamped command ledgers
in the retained packet. The cgroup's observed memory peak reached
approximately its 15 GiB limit, with 1,735 `memory.events max` events and no
OOM/kill events; the peak is shared across the worker and filesystem cache,
not a per-command RSS measurement. Cold/warm cache and host load change these
times substantially. The separate Git evidence retains the two raw tool-build
nonpasses and successful source/native receipts, source URIs, per-module times
and resource snapshots. Initial time/path/parser errors are described in the
author report, not preserved as a complete raw failure transcript. This is a
reproducibility baseline rather than a future runtime guarantee.

## AbelianForget transfer observation

On 2026-09-26, in this transfer's 15 GiB worker cgroup, the matching
Lean v4.34.0-rc2/mathlib cache fetch succeeded (8,892 decompressed cached
files). One `LAKE_JOBS=2 lake --wfail build` of the expanded default library
**and** example targets completed all 2,378 jobs successfully. The retained
build log spans 22:27:31–22:36:33 UTC (about 9m02s); no OOM or kill events
were observed. This is a different workload and cache state from the older
26-module, 2,373-job author baseline above, not a controlled benchmark or a
guarantee for subsequent builds. Keep adequate disk/memory headroom and fetch
the matching cache before building; audit and lightweight metadata checks are
separate steps.

This Markdown ships no doc-gen4 site assets, dependency API website, private
source correspondence, raw proof transcript or full checker output. The
[mathematical guide](Guide.md) covers the significant assumptions and the
[credits](CREDITS.md) distinguish the library's code and third-party tools.
Do not treat a documentation pass or a source-link syntax check as a browser
test, semantic approval, full proof audit, legal clearance, or a release.
