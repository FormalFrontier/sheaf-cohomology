# Library guides and historical native API

This checkout contains **103 Lean files**: 66 subject modules, 35 example leaves,
and the `SheafCohomology` and `SheafCohomologyExamples` roots. Import
`SheafCohomology` for the aggregate library, or import a subject module directly.
The [mathematical and module guide](Guide.md) covers the current library; the
[credits](CREDITS.md) give provenance and third-party attribution.

## Find a result

- **Sheaf cohomology and exactness:** start with the [module guide](Guide.md)
  for resolutions, open cohomology, local cohomology, and flasque and
  quasi-flasque results. The [historical API](API.md) displays declarations
  from the original modules only.
- **Native sheafed spaces and cones:** [native cones](SheafedSpace.md),
  [projection-mate cocones](ConePullbackCocone.md),
  [cone reconstruction](ConeOfPullbackCocone.md),
  [limit construction](SheafedSpaceLimitConstruction.md),
  [limit preservation](SheafedSpaceLimitPreservation.md), and the
  [fixed-base converse](SheafedSpaceConePullbackLimitConverse.md).
- **Diagram maps and coefficients:** [diagram pushforward](DiagramPushforward.md),
  [additive forgetting](AbelianForget.md),
  [coefficient-diagram comparison](AbelianForgetDiagramPushforward.md),
  [cofiltered limits](AbelianSheafedSpaceCofilteredLimits.md), and
  [commutative-ring forgetting](CommRingForget.md).
- **Pullbacks and sections:** [square transitions](SquareTransition.md),
  [cone-pullback limits](ConePullbackLimit.md),
  [local pullback sections](PullbackLocalSections.md), and
  [sections across a cone](ConePullbackSections.md).
- **Native cylinders and stage sections:** [cylinder limits](NativeCylinderLimit.md),
  [open restriction](NativeOpenRestriction.md),
  [stage equality](NativeStageSectionEquality.md),
  [stage lifting](NativeStageSectionLifting.md),
  [stage colimits](NativeStageSectionColimit.md),
  [open-variable naturality](NativeCylinderOpenNaturality.md), and
  [principal-tail changes](NativeCylinderTailChange.md).
- **Global sections and coefficient specializations:**
  [native additive sections](NativeAdditiveGlobalSections.md),
  [additive cylinders](NativeAdditiveCylinderSections.md),
  [ring global sections](NativeCommRingGlobalSections.md),
  [ring cylinders](NativeCommRingCylinderSections.md), and
  [spectral cylinders](NativeSpectralCylinderSections.md).

These guides link to their actual Lean producers and, where useful, ordinary-import
examples. They supplement rather than extend the frozen declaration inventory.

## Historical 26-module reference (September 26, 2026)

[API.md](API.md) preserves native doc-gen4 *display signatures* for 24 original
subject modules plus the then-current aggregate and example roots. Its 556
sites comprise 545 top-level declarations and 11 nested sites; 399 have native
source docstrings, while 157 receive a generic source/guide pointer. Twelve
sites are annotated as source-local instance registrations, not global
instances. The reference neither inventories the current 103 modules nor
certifies elaboration-ready signatures, private declarations or kernel axioms.

The fixed [input manifest](api-manifest.json) binds 26 Lean files and three
project pin files, native JSON/HTML records and the **original**, pre-editorial
`docs/API.md` digest. The original complete generated file and **all 29 exact
input bytes** occur in the [first official public-release history snapshot
`802bfcb6a00c` (September 26, 2026)](https://github.com/FormalFrontier/sheaf-cohomology/tree/802bfcb6a00c82a07058be385a5a18d8ec69dbad).
That public-release history may remain access-controlled while the GitHub mirror
is private; this link does not assert public visibility today. Its tree
`0760e54bc22e850c51a3b98f39ad39adb478b95a` equals the historical
pre-transfer development tree `3a7204971fbbbb0a130335eda04b9d9d2b157267`.
The source originally analyzed by doc-gen4 was
`a9f1a38787d33205c469ff89710563fffb4974fd`; the analyzed commit's
native `sourceUri` identifies provenance, not a claim that its URL is publicly
reachable.

The 24 original subject files **still match** their manifest hashes byte for
byte in this 103-file checkout, so all relative `Frozen source` line links in
[API.md](API.md) refer to the same original source lines here. The aggregate
root, example root, `lakefile.toml` and `lake-manifest.json` differ from their
historical inputs; the pinned `lean-toolchain` still matches. The two roots
have no native declaration display sites. New headers in other modules do not
change any of the frozen source-link targets. Do not use this checkout's
changed roots or dependency graph to claim reproduction of the old output.
The manifest's `api_sha256` deliberately remains the hash of the **original**
generated Markdown in the historical snapshot, not the editorial introduction
of this checkout. These useful historical bindings are not release/build/axiom
attestations for the current library.

## Optional historical reproduction

Use a separate checkout of the exact official historical snapshot above (or
its byte-identical pre-transfer development tree), not current main. Keep an
unchanged separate doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its own toolchain
and manifest. In the historical sheaf checkout, install its pinned Lean,
**successfully fetch the matching mathlib cache before building**, then run:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

Build `doc-gen4` in its **separate** pinned checkout with `lake build doc-gen4`.
Supply that executable's actual absolute path in the historical sheaf checkout:

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
```

The `source_revision` above is **historical metadata**; its URL is not the
public-release snapshot link. Native generation was performed for the older
inputs; no new native run or computation is claimed here. Neither historical
reproduction nor stored-proof replay is a new release requirement. Current
release acceptance separately needs its applicable build, transitive
standard-axiom audit, rights assessment and independent review.
