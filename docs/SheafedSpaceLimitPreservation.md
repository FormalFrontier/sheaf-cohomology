# Preservation of native sheafed-space limits

Import `SheafCohomology.LimitPreservation` for two **named** witnesses in
`AlgebraicGeometry.SheafedSpace`:

```text
preservesLimitForgetOfSpaceCone A S c hc : PreservesLimit S (forget A)
preservesLimitForgetOfHasLimit A S : PreservesLimit S (forget A)
```

The aggregate `SheafCohomology` import also exposes these witnesses. The
private client leaf is registered in `SheafCohomologyExamples`; its imports
are not required to use the public API.

The first takes `S : Jᵒᵖ ⥤ SheafedSpace.{u,w,w} A`, an **actual** cone
`c : Cone (S ⋙ forget A)`, its `hc : IsLimit c`, and
`[HasWeakSheafify (Opens.grothendieckTopology c.pt) A]`. Coefficients
`A : Type u` carry `Category.{w} A`, a `FunLike` presentation of morphisms
on carriers `A → Type w`, `ConcreteCategory.{w} A`, limits and colimits,
preservation of limits and filtered colimits and reflection of isomorphisms
by `CategoryTheory.forget A`, plus `[HasColimitsOfShape J A]`.
The index `J : Type wj` has independent category morphism universe `vj`;
the hypotheses do not assert unrestricted limits of every diagram.
The explicit native universes are those of the prerequisite
`limitConeOfSpaceCone`; the shape object and morphism universes remain independent.

The proof calls `limitConeOfSpaceCone A S c hc`, whose `isLimit` proves the
**constructed** native cone limits. Its `limitConeOfSpaceCone_forget` identifies
the *entire* mapped native cone with the supplied limiting `c`, so `hc`
proves the mapped cone limits. Mathlib's
`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` transfers
this property from one native limiting cone to **every** native limiting
cone of `S`. This does not assume a native `HasLimit`, preservation,
reflection, or a converse about arbitrary native cones.

The second witness uses `[HasLimit (S ⋙ forget A)]` and
`[HasWeakSheafify (Opens.grothendieckTopology
((limit (S ⋙ forget A)) : TopCat)) A]`; it selects `limit.cone` and
`limit.isLimit` of the space diagram and applies the first theorem. Like
the prerequisite `hasLimitOfHasLimitForget`, it requires
`SheafedSpace.{u,w,w} A` and **does not register a global instance**.
Locally install it with `letI : PreservesLimit S (forget A) := ...` to use
`isLimitOfPreserves (forget A) hNative`, `preservesLimitIso`, and
`preservesLimitIso_hom_π` from mathlib. A native `IsLimit hNative` is only
the *input cone* to mathlib's generic preservation API, not a premise for
constructing either preservation witness.

`SheafCohomologyExamples.LimitPreservation` contains import-only private
clients: arbitrary diagrams over `(Fin 3)ᵒᵖ` for both `Type v` and
`AddCommGrpCat.{v}` use local preservation and `isLimitOfPreserves` on
arbitrary limiting native cones; their two distinct nonidentity index
arrows `0 ⟶ 1` and `1 ⟶ 2` check mapped-cone projection equations. The
Type client also invokes mathlib's chosen-limit comparison projection
after installing the existing named native-limit and new preservation
witnesses. An empty `PEmpty.{1}ᵒᵖ` diagram checks arbitrary native cones
and the chosen-base witness. No equality of arbitrary native spaces with
the selected base, or blanket empty-shape reflection, is claimed.

For the pinned dependency graph, cache-first build and full
verification boundaries, see the [project README](../README.md#build-and-verification).
