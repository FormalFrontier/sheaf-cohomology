<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# Forgetting commutative-ring coefficients on native sheafed spaces

The functor `AlgebraicGeometry.SheafedSpace.CommRingForget.underlying` sends
sheafed spaces with `CommRingCat.{v}` coefficients to sheafed spaces with
`Type v` coefficients. It preserves the underlying space and its base maps
strictly; on sheaves it uses the native mathlib `sheafCompose` construction
with `CategoryTheory.forget CommRingCat`. Import
`SheafCohomology.CommRingForget.LimitPreservation` for the entire development,
or import an individual module in `SheafCohomology.CommRingForget`.
`import SheafCohomology` also exposes the producer API. The independent
ordinary-import example is
`SheafCohomologyExamples.CommRingForgetLimitPreservation`.

## Original-cone comparison

`TopCat.Sheaf.CommRingForget.canonicalComponent g A` is the Type-valued
pullback/pushforward adjunction mate of the **original** ring-sheaf unit for
any continuous map `g` between same-universe spaces. The mate equation,
naturality, identity and composition laws accompany the canonical comparison
isomorphism. Here `TopCat.Sheaf.CommRingForget.canonicalComparison` names
the pullback natural transformation. Separately, the fixed-space sheaf functor
preserves colimits of small same-universe filtered diagrams: its comparison is
`colimit.post D (underlyingSheaf Z)`. The theorem `canonicalComparison_stage`
identifies the stage maps of this `colimit.post`, and
`canonicalComparison_isIso` proves it invertible. The construction uses
mathlib's sheafification, ring filtered-colimit and Kan-extension APIs; it
does not redefine them.

For an **actual** diagram and cone, `conePullbackIso` compares the native
pullback-sheaf diagrams associated to the given underlying-space cone.
`conePullbackCocone_forget_ι` identifies the forgotten cocone's legs with
the mates of the given projections. The resulting colimit comparison and
native limit criterion use these original legs, rather than constructing
new projections or assuming that a comparison is an isomorphism.

For `J : Type v` with `[SmallCategory J] [IsFiltered J]` and
`S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v}`,
`SheafedSpace.CommRingForget.preservesCofilteredLimit S` supplies
`PreservesLimit S SheafedSpace.CommRingForget.underlying`. Therefore every
original limiting cone remains limiting after forgetting coefficients.
`preservesCofilteredLimitsOfShape` names the shape-level result without
registering a global instance. The ordinary-import `uniqueLift` example
gives a unique map from any Type-valued cone into the forgotten original
cone, with equations against `underlying.map (m.π.app i)` themselves.
The filtered hypothesis is real: this is not an arbitrary-shape or
empty-index theorem, and no spectrality, nonempty stage, surjective
transition, or replacement-cone premise is needed here.

## Reproduction and attribution

Use this repository's pinned `lean-toolchain` and `lake-manifest.json` from
its root. After fetching the matching precompiled cache successfully, the
relevant targets may be built with:

```sh
lake exe cache get
lake --wfail build SheafCohomology.CommRingForget.LimitPreservation
lake --wfail build SheafCohomologyExamples.CommRingForgetLimitPreservation
```

These are reproduction instructions, not evidence of checks on this
candidate. The direct dependencies are mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the officially
published spectral-stone-duality
`452b7b7be1bea76434cd083b1019a26f96b4ab30`; no incubator checkout
or RingedSpaces dependency is required. Worker-a Hive Task
`hive-request-c57c813632815e9d350373cdfa7741657fb4852a` (UID
`2717d143-2755-441e-83fb-8f9190fbe8f1`) authored the ring bridge by
adapting the published additive counterpart. The precise original and
adaptation credits, including the earlier additive limit-preservation
expression, are in [credits](CREDITS.md); independent destination review,
build and axiom checks are separate from original donor acceptance.
