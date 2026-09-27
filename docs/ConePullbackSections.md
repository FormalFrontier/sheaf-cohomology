<!-- SPDX-License-Identifier: Apache-2.0; Authors: Formal Frontier Agents -->
# Sections across a cone of sheaf pullbacks

Import `SheafCohomology.ConePullbackSections`. This module works
with `TopCat.{v}` and sheaves valued in `Type v`. It needs no spectral,
filtered, limiting-cone, or nonempty-index assumption.

## Section transport

For `f : X ⟶ Y`, `F : Y.Sheaf (Type v)`, `G : X.Sheaf (Type v)`, and
`a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G`,
`SheafCohomology.ConePullbackSections.adjointSectionMap f a U` is the `op U`
component of the actual `pullbackPushforwardAdjunction` mate. The
`restrictedAdjointSectionMap f a U V hV` version additionally restricts from
`f ⁻¹' U` to `V ≤ f ⁻¹' U` in `G`. The unit-only version is
`restrictedUnitSectionMap f F U V hV`. Their components are morphisms in
`Type v`, so they can be applied to sections or composed with other maps.

`restrictedAdjointSectionMap_restrict_source` and
`restrictedAdjointSectionMap_restrict_target` handle nested opens;
`adjointSectionMap_eq_unit_comp` and
`restrictedAdjointSectionMap_eq_unit_comp` identify the adjoint with the
actual unit followed by the component of `a`.
`restrictedUnitSectionMap_eq_unit_comp` identifies the *restricted* unit with
the literal adjunction unit at `op U` followed by the pullback sheaf's
restriction to `V`. There is no separately postulated transport system or
independent coherence framework.

For `q : W ⟶ X`, a triangle `h : q ≫ f = p`, and
`V ≤ f ⁻¹' U`, `T ≤ q ⁻¹' V`, the theorem
`restrictedAdjointSectionMap_triangle f h a U V T hV hT` identifies the
restricted adjoint of the published `SheafedSpace.triangleMap (Type v) h a`
along `p` with the restricted adjoint of `a` along `f` **followed by** the
restricted unit along `q`. `triangleOpen_le` constructs `T ≤ p ⁻¹' U`
from these inputs; no additional compatibility hypothesis is imposed.
`adjointSectionMap_triangle_top` supplies the corresponding adjoint equation on
maximal opens; `triangleMap_unit_top` states it explicitly as the unit along
`p`, followed by `triangleMap` at `op ⊤`, equals the adjoint along `f`,
followed by the unit along `q`. Its proof uses the canonical `pullbackCompInv`
and the actual composite/direct adjunction comparison.

## Arbitrary native diagrams

For any small `J`, a contravariant native diagram
`N : Jᵒᵖ ⥤ SheafedSpace (Type v)`, and any cone
`c : Cone (N ⋙ SheafedSpace.forget (Type v))`, the transformation
`coneSections N c` has domain **exactly** `N.rightOp ⋙ SheafedSpace.Γ`
and codomain
`SheafedSpace.conePullback (Type v) N c ⋙
 SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)`.
The component at `i` is the stage projection's adjunction unit at `op ⊤`
(`coneSections_app`). Its naturality combines the triangle law with
`SheafedSpace.sheafMate_adjoint` applied to `N.map arrow.op` for each
arrow `arrow : i ⟶ j`. When both individual colimits exist,
`colimit_ι_colimMap_coneSections` identifies every leg of the ordinary
`colimMap (coneSections N c)`; no named colimit-map wrapper is introduced.

The named import-only client theorems in
`SheafCohomologyExamples.ConePullbackSections` exercise arbitrary
nested opens, the literal-unit/restriction triangle via `literalUnitsTriangle`,
and the unrestricted-category cone components, naturality, and colimit legs.
This API constructs section transport only: it asserts
neither invertibility of the colimit map nor finite-stage equality, descent,
gluing, or source-specific coverage.

## Provenance and status

Author of this native contribution: worker-a Hive Task
`hive-request-56a0f46868a5a666cdc4e1ce2d7423802e462456`, UID
`6168c7bc-d47b-4305-a538-58d1350272d0`, based on incubator commit
`7f4048bdf110f4f49e19908567443aabb9fdc8ab`. That incubator input's official
SheafCohomology dependency was commit `e4c7d681e0913fc1dde266cfcfc37763f1d47785`.
The destination uses its own existing modules and depends only on mathlib's
pinned package graph; it has no self-dependency or incubator dependency.
Repair author: worker-a Hive Task
`hive-request-6d526071fadec30d7ff2b4abfed7d988d35a78da`, UID
`d4885694-78ac-4ce2-bc13-f81029f15673`, starting from unaccepted
candidate `e3b7c1f1b7e8c37104f22c0094831eaccb86036d` after the
independent review at `3100c3d818fb4a1435c9ef2582179b2f3a0fa00d`.
The repaired incubator leaf `dd4ba173e5dda37074b47a16c4fa7647305149fe`
received a fresh independent review by worker-b Hive Task
`hive-request-71f983a9268c32fce086bf8f2f49cddf5c6eeb15`, UID
`45597500-b870-4e33-b97f-ca2408f918fb`, at report commit
`f2cab0cb921b5cf81a3db9e99377a13903fbbbb4` and source-maintainer
acceptance for transfer. The earlier review's objections still apply to the
superseded original leaf, not to the repaired leaf.

The namespace/import adapter into this library is by worker-a Hive Task
`hive-request-8a7211e66bf0303b4ffc778195cdf17b95093b09`, UID
`e1cd2f5b-de9b-4f1a-b4a9-6e7df9d766dd`, at transfer commit
`e770f0fa714c83bc735b7ed22f3abeb853fe7cdb`. Anchor registered both unchanged
Lean leaves in the aggregate roots and updated navigation, credit and metadata.
This 63-module destination registration still needs independent final
destination/release review and applicable combined checks, owner acceptance,
integration and verified publication. Focused destination author checks and
the source-leaf review do not substitute for these separate gates.

The proof **expression** of private `adjoint_comp` closely adapts Anchor
(Source Maintainer)'s theorem `adjointTransition_pullbackTransitionComposite`
in `Research/fk-proposition-3-1-10-pullback-coherence-scratch.lean` (roughly
lines 84–117): the adjunction-uniqueness comparison, `change`, and successive
`rw` steps have the same structure. It also closely follows the published
`mateComp` proof in `SheafCohomology/ConePullback.lean` (roughly lines 76–108)
at the official commit above. The source- and target-restriction proofs
`restrictedAdjointSectionMap_restrict_source` and
`restrictedAdjointSectionMap_restrict_target` closely adapt proof steps in
Anchor's `Research/fk-proposition-3-1-10-adjoint-transition-naturality-scratch.lean`.
The earlier `Research/fk-proposition-3-1-10-stage-section-transport-probe.lean`
informs the nested-triangle idea; the native triangle and `coneSections`
construction use the published sheaf/sheafed-space APIs directly and are new
relative to the old dependent stage-section framework, which is **not** copied
or imported here. The frozen donor repository is
`source-fujiwara-kato-rigid-geometry-i` commit
`e266a5076df34934171cc284ba8f2834e56f8c78`, tree
`824767793ae40f9e03b3217e572f3cf43d91302c`;
the donor code is **not imported**. These are provenance credits, not an
acceptance, review, integration, or source-formalization claim.
