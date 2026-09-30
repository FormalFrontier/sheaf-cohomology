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
