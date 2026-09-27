# Native sheafed-space cones and additive forgetting

Import `SheafCohomology.ConePullback` for cones of native sheafed spaces,
`SheafCohomology.AbelianForget.SheafedSpace` for the additive-to-Type
forgetful functor, or `SheafCohomology` for both. These are supplements to
the [historical 26-module API reference](API.md), not part of its frozen
generated inventory. Their namespaces are `AlgebraicGeometry.SheafedSpace`
and `AlgebraicGeometry.SheafedSpace.AbelianForget`, respectively.

## Sheaves over any underlying-space cone

In [`ConePullback.lean`](../SheafCohomology/ConePullback.lean), let
`J : Type wj` be any `Category.{vj} J` and
`S : Jᵒᵖ ⥤ SheafedSpace A` a native contravariant diagram. Given *any*
`c : Cone (S ⋙ SheafedSpace.forget A)`, `conePullback A S c` is a functor
`J ⥤ c.pt.Sheaf A`. It requires neither a limiting cone nor a filtered or
nonempty index category. The coefficient assumptions are **not** arbitrary:
`[Category.{w} A]`, a compatible `FunLike` family for its concrete morphisms,
`[ConcreteCategory.{w} A FA]`, `[HasColimits A]`, `[HasLimits A]`,
`[PreservesLimits (CategoryTheory.forget A)]`,
`[PreservesFilteredColimits (CategoryTheory.forget A)]` and
`[(CategoryTheory.forget A).ReflectsIsomorphisms]`. The concrete morphism
family `FA` and carrier family `CA` also share the stated universe `w`.

`sheafMate A f` is the inverse-image mate of the **actual** native arrow
`f : X ⟶ Y`, from pullback of `Y.sheaf` to `X.sheaf`;
`sheafMate_adjoint`, `sheafMate_id` and `sheafMate_comp` give its adjunction,
identity and composition laws. `triangleMap A triangle a` transports an
inverse-image sheaf arrow `a` across a commuting triangle of spaces; its
`triangleMap_id` and `triangleMap_comp` laws use native pullback coherence.

For `a : i ⟶ j` in `J`, the cone triangle equates
`c.π.app (op j) ≫ (S.map a.op).hom.base` with `c.π.app (op i)`.
`conePullbackMap A S c a` applies `triangleMap` to the mate of this
**actual** arrow `S.map a.op : S.obj (op j) ⟶ S.obj (op i)`;
`conePullbackObj` supplies each pulled-back stage sheaf. Their identity
and composition laws construct the functor. The public simp lemmas
`conePullback_obj` and `conePullback_map` expose its objects and arrows.
The [private import-only clients](../SheafCohomologyExamples/ConePullback.lean)
test arbitrary Type- and additive-valued `Fin 3` diagrams, both index arrows,
composable maps, and an explicit empty cone vertex. The index arrows are
nonidentity; their images under an arbitrary diagram need not be.

## Forgetting additive sheafed spaces

In [`AbelianForget/SheafedSpace.lean`](../SheafCohomology/AbelianForget/SheafedSpace.lean),
`underlying : SheafedSpace AddCommGrpCat.{v} ⥤ SheafedSpace (Type v)` uses
mathlib's coefficient `mapPresheaf` on objects **and actual arrows** and the
existing `underlyingSheaf`/`sheafCompose` sheaf condition. The simp lemmas
`underlying_obj_carrier`, `underlying_obj_presheaf`,
`underlying_obj_sheaf`, `underlying_map_base` and `underlying_map_c`
identify the strict carrier, presheaf, sheaf, base-map and structure-map
equalities. `underlying_forgetToPresheafedSpace` and `underlying_forget`
identify the corresponding strict functor equalities. For any native arrow
`f : X ⟶ Y`, `underlying_map_pullback_mate f` identifies the Type-valued
adjunction mate of its *actual* forgotten structure map with
`canonicalComponent f.hom.base Y.sheaf` followed by the forgotten additive
mate. There is no freely chosen compatible sheaf arrow or extra premise.
The [private import-only clients](../SheafCohomologyExamples/AbelianForgetSheafedSpace.lean)
exercise actual arrows, composable chains, identities, and arrows over
explicit empty carriers.

These APIs make no assertion of a cone/forgetful diagram isomorphism, a
colimit comparison, a final geometric endpoint, a complete theory, or
source-level coverage. See [forgetting additive sheaves](AbelianForget.md)
for the existing pullback and filtered-colimit comparisons.
