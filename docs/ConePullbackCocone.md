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
The aggregate `SheafCohomology` imports this module, and
`SheafCohomologyExamples` imports its private client. This registration and
the guide/metadata assembly do not themselves establish a successful combined
build, independent destination acceptance or verified publication.

## Provenance

The mathematical expressions originate with Formalization Worker B, Hive Task
`hive-request-b5d71038ee1c27e92bd1d66f62b21001a79f2069` (UID
`001c2dd6-70cd-4f36-92a3-0bee18fb582a`), incubator commit
`e32952df2893d49f76b8fe96a63db3defd3a4381`. Its prerequisite
`ConePullback` expressions originated with Worker B Task
`hive-request-a5c686fef9733b91207a12bdbe674244008553c9` (UID
`f70328b3-10f7-4bbc-a451-4678e9530731`). Worker A Hive Task
`hive-request-314f8ea55794f67df587aaab888cb76a998d3007` (UID
`285a5ea5-e220-4df1-8088-816b66f61521`) transfers the original
cocone expressions and adapts imports, client visibility/module names,
documentation and the repository's Apache-2.0 collective-author headers.
This credits expression origin without attributing an unverified human author
or making a source-coverage claim.
