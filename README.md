# sheaf-cohomology

Reusable Lean foundations for sheaf cohomology, compact-open sections,
cohomological functors, and forgetting abelian-group structure on sheaves.
It also provides native sheafed-space cone pullbacks and an additive-to-Type
forgetful functor on sheafed spaces.

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). The library builds on independently reviewed
mathematical developments; it does not claim that any complete mathematical
source is formalized. The Lake package declares version `0.1.0`;
the `v0.4` in `formalization.yaml` identifies the metadata schema, not a release.

## Mathematical scope

The initial units prove that evaluation of sheaves valued in a suitable
concrete category on a compact open preserves filtered colimits. They define
quasi-flasque sheaves categorically, show that this is exactly surjectivity of
the restriction maps for set-valued sheaves, and prove that same-size filtered
colimits preserve quasi-flasqueness on compact prespectral quasi-separated
spaces. The resulting set-valued theorem currently has a common universe for
the space, coefficient types, and indexing category; no independently varying
universe wrapper is claimed.

For abelian sheaves, the library identifies degree-zero sheaf cohomology
naturally with global sections and transfers the preservation theorem across
that identification. For short exact sequences with quasi-flasque kernel, it
proves surjectivity on sections over compact opens; in particular, global
sections are exact on compact prespectral quasi-separated spaces. It also shows
that quasi-flasque sheaves are closed under quotients in such short exact
sequences. These exactness results currently follow mathlib's same-universe
topological-sheaf API. The compact-open implementation exposes the canonical
sheafification-colimit comparison needed for these and later cohomological
applications.

For spaces and coefficients in a common universe, the library also constructs
a flasque injective envelope as a product of injective skyscraper sheaves and
uses its quasi-flasque cokernel for dimension shifting. This proves that
quasi-flasque abelian sheaves on compact prespectral quasi-separated spaces
have trivial positive-degree sheaf cohomology. The accepted compact-open
exactness interface couples the space and coefficient universes; this result
does not provide a wrapper for independently varying universes.

The library also constructs a functorial stalk-skyscraper flasque resolution,
proves its augmentation is a quasi-isomorphism, and compares positive-degree
sheaf cohomology with the homology of terminal-open sections. Its one-step
dimension-shift comparison is natural in the input sheaf. This API currently
uses universe zero (`TopCat.{0}` and the corresponding small coefficient and
Ext types) in its sheaf-specific construction. On
compact prespectral quasi-separated spaces, the resolution is also packaged as
an Ext-acyclic resolution, functorially in the input sheaf. The degree-zero Ext
complex of this package is naturally identified with the complex of sections
of the flasque resolution on the terminal open, including the induced homology
identification.

For a continuous map, the library also packages the Ext-based cohomology
presheaf on the source as a local-cohomology presheaf on the target and defines
its functorial sheafification with the canonical sheafification map. The
library identifies the value of the cohomology presheaf on an open with the
cohomology of the restricted sheaf on its over-site. Its intrinsic over-site
restriction maps satisfy identity and composition and agree with the maps of
the cohomology presheaf under this identification. In positive degree, the
sheafified local-cohomology functor is naturally isomorphic to right-derived
pushforward. The open-over-site and positive right-derived comparison APIs use
a common universe parameter for spaces, coefficients, and Ext groups; the
comparison does not cover degree zero or
independently varying universes.

For a spectral map from a prespectral quasi-separated space to a prespectral
space, right-derived pushforward preserves filtered colimits in every natural
degree. The public API identifies the comparison with the literal
`CategoryTheory.Limits.colimit.post` morphism and records its equation on each
stage of the filtered diagram. The proof treats degree zero through compact-open
sections and positive degrees through sheafified local cohomology. It currently
uses universe zero for spaces, coefficients, diagrams, and Ext groups;
it assumes neither sobriety nor Noetherian or finite-cohomological-dimension
hypotheses.

The library also exposes canonical identity and composition comparisons for
pullback of sheaves, including both identity triangles and the
triple-composition coherence law. This supports diagrams transported across
varying topological spaces without treating pullback as strictly functorial.
This interface retains mathlib's current requirement that the space universe
also contain coefficient carriers and morphisms; the coefficient category's
object universe remains independent.

For a continuous map and an open subspace of its target, the library constructs
the canonical inverse-image open square and the direct- and inverse-image
comparisons for sheaves of types. It proves that these comparisons are mates
and exposes the resulting counit equation. No surjectivity assumption is made;
the construction applies equally to empty and whole opens and spaces.

For any continuous map between topological spaces in a common universe, the
underlying-Type-sheaf functor commutes with additive-sheaf pullback via the
canonical native-adjunction mate. This **particular** arrow is natural and
invertible, and satisfies the native identity and composition equations. For
any small filtered diagram in that universe, forgetting additive structure
preserves its colimit: the comparison is the literal `colimit.post` with its
stage-leg equation under the ordinary colimit instances. Neither result
requires spectral or nonempty-space hypotheses. These theorems do not supply a
universe-crossing wrapper or prove a complete source result.

For a commuting square of continuous maps and a pullback stage morphism,
the library constructs the canonical counit-defined transition between
pushforwards. Its adjoint is the forward strict pushforward comparison;
transitions are natural in the stage target and respect identities and
arbitrary two-square pasting. Coefficients satisfy the native concrete-category
pullback-adjunction assumptions, with the space universe containing their
carriers and morphisms. No spectral or nonempty-space hypothesis is required.
This generic square API does not yet assert compatibility with forgetting
abelian structure.

For any native contravariant sheafed-space diagram and **any** cone of its
underlying spaces, `SheafCohomology.ConePullback` pulls the stage sheaves back
to the cone vertex; stage maps are mates of the diagram's actual arrows.
This does not require a limiting, filtered or nonempty cone, but does require
the concrete coefficient category's native pullback-adjunction assumptions,
including limits and colimits, forgetful preservation of limits and filtered
colimits, and reflection of isomorphisms. The native
`SheafCohomology.AbelianForget.SheafedSpace` functor forgets additive structure
via `mapPresheaf` and proves the actual-arrow mate law for same-universe
additive sheafed spaces. Neither API claims a cone/forgetful diagram
isomorphism, colimit comparison, final geometric endpoint or source coverage.
See the [native sheafed-space guide](docs/SheafedSpace.md).

This repository is organized around reusable mathematics. Source-specific
interpretation, provenance, correspondence, and coverage remain in the relevant
source-metadata repositories. Anchor is responsible for the initial integration
on behalf of the Source-maintainers team.

Project repository: `https://github.com/FormalFrontier/sheaf-cohomology`.
Access is subject to the repository's permissions; this URL does not imply
public visibility.

## Public entry points

Use `import SheafCohomology` for the aggregate API, or a subject module for a
smaller import. The module-system readiness assembly re-exports the existing
interfaces; implementation helpers remain private.

For the forgetful functor and its comparisons, import
`SheafCohomology.AbelianForget.Pullback` and/or
`SheafCohomology.AbelianForget.FilteredColimits`, or import
`SheafCohomology.AbelianForget.SquareTransition` for compatibility with the
native square transition; these import the needed forgetful and square APIs. The
[`AbelianForget` declaration guide](docs/AbelianForget.md) gives exact
hypotheses and links to shipped code. A root-import example in
`SheafCohomologyExamples/AbelianForgetPullback.lean` specializes
`TopCat.Sheaf.AbelianForget.canonicalComponent_isIso` to the empty space;
`SheafCohomologyExamples/AbelianForgetFilteredColimits.lean` specializes
`preservesFilteredColimits` to `ℕ`. These are private named examples.
Five further private clients in
`SheafCohomologyExamples/AbelianForgetSquareTransition.lean` exercise arbitrary
additive stages, target postcomposition, identity, the empty space and pasted
squares. The square law compares the actual additive and Type-valued native
transitions, not an arbitrary choice of transport or an additive endpoint.

For generic commuting-square transitions, import
`SheafCohomology.SquareTransition` or the aggregate root. The
[SquareTransition guide](docs/SquareTransition.md) documents the forward mate,
target naturality, identities and arbitrary pasting with exact coefficient
assumptions; eleven focused private examples cover Type, abelian groups and
empty spaces.

| Subject | Module and representative interface |
| --- | --- |
| Compact-open sections | `CompactOpenSections`: canonical section comparison and colimit preservation |
| Quasi-flasqueness | `QuasiFlasque`: `TopCat.Sheaf.IsQuasiFlasque` and its set-valued criterion |
| Degree zero | `DegreeZero`: `SheafCohomology.DegreeZero.functorHZeroIsoSections` |
| Acyclic resolutions | `AcyclicResolution`, `FlasqueResolution`, `FlasqueAcyclicResolution` |
| Local and open cohomology | `LocalCohomology`, `OpenCohomology`: presheaf maps and intrinsic over-site restriction |
| Positive derived comparison | `OpenCohomologyRightDerived`: `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived` |
| Higher-image colimits | `HigherDirectImageFilteredColimit`: canonical comparison and stage equation in every natural degree |
| Pullback and open base change | `PullbackCoherence`, `OpenBaseChange`: coherent comparisons and the open-square mate |
| Commuting-square transitions | `SquareTransition`: canonical transition, forward strict mate, naturality and pasting |
| Forgetful square transitions | `AbelianForget.SquareTransition`: strict pushforward compatibility and additive-to-Type native transition equation |
| Native sheafed-space cones | `ConePullback`: arbitrary underlying-space cones and actual-arrow mates |
| Forgetful sheafed spaces | `AbelianForget.SheafedSpace`: strict coefficient forgetting and native arrow mate |

All module names in the table are prefixed by `SheafCohomology.`. Consult their
declaration types for the precise category, sheafification, Ext and universe
assumptions. In particular, a common universe parameter is different from a
construction fixed at universe zero, and a positive-degree comparison is not
an all-degree comparison. Quasi-flasqueness only controls restriction from the
terminal open to compact opens; it is weaker than flasqueness.

The [module and assumptions guide](docs/Guide.md) covers all shipped subject
modules. The [historical native-generated API signatures](docs/API.md) cover
the original 26-module source snapshot (including the then-unmodified roots);
the [lightweight AbelianForget guide](docs/AbelianForget.md) and
[SquareTransition guide](docs/SquareTransition.md) cover the five subjects
in that historical supplement group; the
[native sheafed-space guide](docs/SheafedSpace.md) documents two further
subjects. Of the old 556 native display sites,
399 carry source docstrings; the other 157 explicitly mark their absence and
point generically to the source and module guide, not separately authored
per-site explanations. These pointers do not certify complete semantic
documentation of the API. The native display inventory is separate from the
private and generated declaration inventory needed for proof verification.
Import the aggregate root or only the required subject module; importing
`SheafCohomologyExamples` is unnecessary.

`SheafCohomologyExamples.lean` is the public-root example target of the
readiness assembly and imports six additional example leaves. All examples use
named private declarations so their proof bodies can be included in
verification without adding a second public mathematical API.
No client should import or unfold private implementation helpers.

## Build and checks

Use elan with `leanprover/lean4:v4.34.0-rc2`, exactly as recorded in
`lean-toolchain`. The direct dependency is mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; `lake-manifest.json` pins its complete
nine-package graph. There is no dependency on another Formal Frontier library
or on a source-research checkout. A distributed checkout needs no internal
service or VPN to build; the declared mathlib dependencies use upstream URLs.

From the repository root, fetch the matching dependency cache successfully before
building. Do not use a source rebuild as an implicit substitute for a failed cache
fetch:

```sh
lake exe cache get
lake --wfail build
lake --wfail build SheafCohomologyExamples
```

The default build includes the library and checked example target. Exact check
results and independent review must bind the final combined revision; author
checks of an earlier input are not independent approval of the assembly.

The computational release checks are a successful build with the pinned Lean
and dependency graph and a complete transitive axiom audit in the built
environment. The audit covers every repository declaration, including private
declarations and examples, and dependencies reached from them. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted; `sorryAx` and any additional
axiom fail. Use actual Lean `#print axioms` or `Lean.collectAxioms` output, not a
source grep or a selected list that omits declarations. Applicable results can
be reused when their Lean, build and dependency inputs are unchanged; docs-only
edits do not require another build. The ordinary Lean build checks the proofs;
a separate stored-body replay is not an additional release prerequisite.

The [generation instructions](docs/README.md) explain the native documentation
tool and pinned source binding. Existing applicable documentation is reused and
inspected; generating it is neither proof checking nor release acceptance.
See [credits and third-party provenance](docs/CREDITS.md).

## References, attribution and status

The library uses Lean and mathlib's native categories, limits, sheafification,
stalks, Ext groups, injective resolutions and right-derived functors. Mathematical
background includes classical sheaf cohomology and the compact-open and
quasi-flasque arguments motivating the development in Kazuhiro Fujiwara and
Fumiharu Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). These references concern
mathematical ideas; no source PDF or substantial source excerpt is bundled.

Formal Frontier AI agents developed the Lean code, examples and documentation,
with distinct agent executions providing independent development review. Anchor
has coordinated this library; Beacon, Lattice, Atlas and the attributed
formalization-worker executions have contributed reviews or development recorded
in the repository history. This is not a claim of human or source-author approval.
Collective project author credit does not identify a copyright holder or replace
applicable third-party credit and license terms.

The exact accepted development `main` at
`a9f1a38787d33205c469ff89710563fffb4974fd` includes separately reviewed
module/public-use and metadata readiness work (issue 34, ordinary review 3006,
owner 34-40581 and protected integration 40588; verification 40654/40674).
Those historical bounded checks are distinct from revision-specific release
assessment. The latter combines the applicable build and complete standard-axiom
audit with independent inspection of source correspondence, API claims,
documentation, metadata, code organization, licensing and attribution, file
hygiene, exact dependency pins, and release-tree/history requirements. Promotion
and verification of the mirrored commit, ref and destination are separate
publication operations. See `formalization.yaml` for the bounded self-report;
schema validity is not mathematical or legal certification.
