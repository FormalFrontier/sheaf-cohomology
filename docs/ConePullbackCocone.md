# Cocones from native sheafed-space cones

Import `SheafCohomology.ConePullbackCocone` directly; it publicly imports
`SheafCohomology.ConePullback`. The declarations live in
`AlgebraicGeometry.SheafedSpace`. For the underlying diagram construction and
its maps, see [native cone pullbacks](SheafedSpace.md#sheaves-over-any-underlying-space-cone)
and [`ConePullback.lean`](../SheafCohomology/ConePullback.lean).

Let `J : Type wj` carry `Category.{vj} J`, let
`S : Jᵒᵖ ⥤ SheafedSpace A`, and let **`c : Cone S`** be a cone of *actual
sheafed spaces*, not only a cone of their underlying topological spaces.
The construction has type

```lean
SheafedSpace.conePullbackCocone A S c :
  Cocone (SheafedSpace.conePullback A S ((SheafedSpace.forget A).mapCone c))
```

Its point is definitionally `c.pt.sheaf`, by the simp lemma
`conePullbackCocone_pt`. The leg at `i : J` is definitionally
`sheafMate A (c.π.app (op i))`, by `conePullbackCocone_ι_app`.
Here `sheafMate` is the inverse-image mate of the *native* sheafed-space
projection, not an arbitrary arrow between pulled-back sheaves.

For `a : i ⟶ j`, the opposite-index diagram gives
`S.map a.op : S.obj (op j) ⟶ S.obj (op i)` and the native cone equation
`c.π.app (op j) ≫ S.map a.op = c.π.app (op i)`. The sheaf cocone equation is

```lean
(SheafedSpace.conePullback A S ((SheafedSpace.forget A).mapCone c)).map a ≫
  SheafedSpace.sheafMate A (c.π.app (op j)) =
    SheafedSpace.sheafMate A (c.π.app (op i))
```

`conePullbackCocone_triangle` proves it using `sheafMate_triangle`: the
native triangle is transported through `congrArg` on `hom.base`, followed by
the inverse-image mate composition law and `triangleMap`. No independent
commutativity hypothesis is required.

The coefficient category has `Category.{w} A`, compatible `FunLike` and
`ConcreteCategory.{w} A FA` data with carrier `CA : A → Type w`,
`HasColimits A`, `HasLimits A`, and `CategoryTheory.forget A` preserving
limits and filtered colimits and reflecting isomorphisms. Coefficient objects
have universe `u`; index objects and morphisms have independent universes
`wj` and `vj`. These are the same hypotheses as the imported
`conePullback` API, not a claim about arbitrary coefficients.

The [private import-only clients](../SheafCohomologyExamples/ConePullbackCocone.lean)
instantiate arbitrary `Type v` and `AddCommGrpCat.{v}` native `Fin 3`
diagrams/cones, two nonidentity index arrows, their composite and identities.
Their diagram images may nevertheless be identities. A supplied sheaf on
`TopCat.of PEmpty` gives a genuine empty-carrier native cone whose projection
leg satisfies the same mate equation. When the pulled-back diagram has a
colimit, the client uses ordinary `colimit.desc` to obtain a map from its
colimit to `c.pt.sheaf`; colimit existence is a conditional premise of that
client, not part of the cocone construction. These clients use ordinary imports
and private declarations in `SheafCohomologyExamples.ConePullbackCoconeClient`,
instead of the original public imports and public test namespace. Their
generated/private auxiliaries belong to the client module's actual Lean origin,
not to the public API; the original unnamed comparison example is now a named
private definition with the identical type and expression.

No limiting-cone, colimiting-cocone, filteredness, nonemptiness, stage
isomorphism, geometry, endpoint, or forgetful compatibility theorem is asserted.

The aggregate library imports this module; the example library imports
its private client.
