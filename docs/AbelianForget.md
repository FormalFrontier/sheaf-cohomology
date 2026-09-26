# Forgetting abelian-group structure on sheaves

Import `SheafCohomology.AbelianForget.Pullback` for the pullback comparison,
`SheafCohomology.AbelianForget.FilteredColimits` for filtered colimits, or
`SheafCohomology` for both. The functor alone lives in
`SheafCohomology.AbelianForget.Basic`. All names below are in
`TopCat.Sheaf.AbelianForget`; the exact Lean signatures and proof dependencies
are in the linked shipped files. This lightweight supplement covers the new
modules, **not** the historical 26-module native [API reference](API.md).

## Underlying sheaf

[`underlyingSheaf`](../SheafCohomology/AbelianForget/Basic.lean#L28) takes
`Z : TopCat.{v}` and is the functor
`Z.Sheaf AddCommGrpCat.{v} ⥤ Z.Sheaf (Type v)`. It is the native
`sheafCompose` of the forgetful functor with the Grothendieck topology of
opens. It does not assume a spectral or nonempty space.

## Pullback

Fix `X Y : TopCat.{v}`, a continuous `g : X ⟶ Y`, and an additive sheaf
`A : Y.Sheaf AddCommGrpCat.{v}`. Neither space nor the map has an additional
geometric hypothesis. The following declarations are in
[`Pullback.lean`](../SheafCohomology/AbelianForget/Pullback.lean):

| Declaration | Meaning and actual parameters |
| --- | --- |
| [`canonicalComponent`](../SheafCohomology/AbelianForget/Pullback.lean#L34) | Arrow from `g`-pullback of the forgotten `A` to forgetting the additive `g`-pullback. **Defined** as the native Type-valued pullback/pushforward adjunction mate of the forgotten additive unit; parameters `g`, `A`. |
| [`canonicalComponent_mate`](../SheafCohomology/AbelianForget/Pullback.lean#L42) | Applying the Type-valued adjunction's hom equivalence to that arrow equals the forgotten additive adjunction unit; `g`, `A`. |
| [`canonicalComponent_mate_map`](../SheafCohomology/AbelianForget/Pullback.lean#L50) | Mate equation after a map `a : (pullback AddCommGrpCat g).obj A ⟶ B`, for `B : X.Sheaf AddCommGrpCat.{v}`; `g`, `A`, `B`, `a`. |
| [`canonicalComponent_naturality`](../SheafCohomology/AbelianForget/Pullback.lean#L69) | Naturality with respect to an additive-sheaf morphism `a : A ⟶ B` on `Y`; `g`, `a`. |
| [`canonicalComparison`](../SheafCohomology/AbelianForget/Pullback.lean#L92) | Natural transformation between the two composed functors, with components the native mates; `g`. |
| [`canonicalComparison_app`](../SheafCohomology/AbelianForget/Pullback.lean#L101) | Simplification identifying each component with `canonicalComponent g A`; `g`, `A`. |
| [`canonicalComponent_isIso`](../SheafCohomology/AbelianForget/Pullback.lean#L387) | Invertibility of this particular mate for every `g`, `A`, established through presheaf pullback and sheafification. |
| [`canonicalComparisonIso`](../SheafCohomology/AbelianForget/Pullback.lean#L393) | Natural isomorphism with forward components `canonicalComponent`; `g`. |
| [`canonicalComparisonIso_hom_app`](../SheafCohomology/AbelianForget/Pullback.lean#L401) | Simplification identifying the forward component with the canonical mate; `g`, `A`. |
| [`inverseComparisonIso`](../SheafCohomology/AbelianForget/Pullback.lean#L406) | Reverse natural isomorphism, the symmetry of `canonicalComparisonIso`; `g`. |
| [`inverseComparisonIso_inv_app`](../SheafCohomology/AbelianForget/Pullback.lean#L412) | Simplification identifying its inverse component with the canonical mate; `g`, `A`. |
| [`canonicalComponent_id`](../SheafCohomology/AbelianForget/Pullback.lean#L439) | Mate compatibility with mathlib's native identity-pullback maps; `Z : TopCat.{v}`, `A : Z.Sheaf AddCommGrpCat.{v}`. |
| [`canonicalComponent_comp`](../SheafCohomology/AbelianForget/Pullback.lean#L450) | Mate compatibility with mathlib's native composition-pullback maps; `X Y Z : TopCat.{v}`, `f : X ⟶ Y`, `h : Y ⟶ Z`, `A : Z.Sheaf AddCommGrpCat.{v}`. |

## Filtered colimits

Let `Z : TopCat.{v}`, `I : Type v` with `[SmallCategory I]`, and
`D : I ⥤ Z.Sheaf AddCommGrpCat.{v}`. See
[`FilteredColimits.lean`](../SheafCohomology/AbelianForget/FilteredColimits.lean)
for the exact binders and the explicit native `HasColimit` requirements:

| Declaration | Meaning and actual assumptions |
| --- | --- |
| [`preservesFilteredSheafColimit`](../SheafCohomology/AbelianForget/FilteredColimits.lean#L59) | `PreservesColimit D (underlyingSheaf Z)` with `[IsFiltered I]`; obtained using presheaf left Kan extension and sheafification. |
| [`preservesFilteredColimits`](../SheafCohomology/AbelianForget/FilteredColimits.lean#L87) | `PreservesColimitsOfShape I (underlyingSheaf Z)` with `[IsFiltered I]`; a named witness, **not** a new global/scoped instance. |
| [`canonicalComparison_stage`](../SheafCohomology/AbelianForget/FilteredColimits.lean#L92) | For both `[HasColimit D]` and `[HasColimit (D ⋙ underlyingSheaf Z)]`, the actual `colimit.post D (underlyingSheaf Z)` composed with stage leg `i : I` equals the image of the additive stage leg; this equation does **not** require `[IsFiltered I]`. |
| [`canonicalComparison_isIso`](../SheafCohomology/AbelianForget/FilteredColimits.lean#L99) | `IsIso (colimit.post D (underlyingSheaf Z))` with `[IsFiltered I]` and both ordinary `HasColimit` instances; the isomorphism is the literal native map, not a separately chosen arrow. |

Native `CategoryTheory.Sheaf.instHasColimitsOfShape` supplies the additive and
Type-valued colimits in the natural-number client when appropriate. These are
same-universe APIs, not arbitrary universe-crossing wrappers or a source-level
completion claim. The checked
[`AbelianForgetPullback`](../SheafCohomologyExamples/AbelianForgetPullback.lean)
and [`AbelianForgetFilteredColimits`](../SheafCohomologyExamples/AbelianForgetFilteredColimits.lean)
clients use the aggregate `SheafCohomology` import. Their 15 named private
examples exercise arbitrary maps and mates, identity, composition, empty spaces,
and natural-number filtered diagrams; they are not a second public API.
