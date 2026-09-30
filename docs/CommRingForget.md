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
