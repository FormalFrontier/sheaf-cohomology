# Fixed-base converse for limits of sheafed spaces

Import `SheafCohomology.ConePullbackLimitConverse` for the converse of the
[native limit criterion](ConePullbackLimit.md) for **actual cones**.

The `SheafCohomology` root exports this producer;
`SheafCohomologyExamples` imports its private client module.

```lean
import SheafCohomology.ConePullbackLimitConverse

#check AlgebraicGeometry.SheafedSpace.isColimit_conePullbackCocone_of_isLimit
#check AlgebraicGeometry.SheafedSpace.nonempty_isLimit_iff_isColimit_conePullbackCocone
```

For `S : Jᵒᵖ ⥤ SheafedSpace A` and an actual `C : Cone S`, supply **both**
`hbase : IsLimit ((SheafedSpace.forget A).mapCone C)` and
`hC : IsLimit C`. The first result gives the universal property of the
**actual projection-mate cocone**:

```text
SheafedSpace.isColimit_conePullbackCocone_of_isLimit A S C hbase hC :
  IsColimit (SheafedSpace.conePullbackCocone A S C)
```

It is a noncomputable `def`: the `IsColimit` witness contains a Type-valued
descent map. With the same actual base-limit witness,
`nonempty_isLimit_iff_isColimit_conePullbackCocone A S C hbase` states
`Nonempty (IsLimit C) ↔ Nonempty (IsColimit (conePullbackCocone A S C))`.
Its reverse implication reuses the already available forward criterion; it
does not duplicate that construction.

## Assumptions and range

The producer has universes `w u vj wj`: `A : Type u` carries
`Category.{w} A`, `FunLike (FA X Y) (CA X) (CA Y)` with `CA : A → Type w`,
`ConcreteCategory.{w} A FA`, `HasColimits A`, and `HasLimits A`.
`CategoryTheory.forget A` preserves limits and filtered colimits and reflects
isomorphisms. Independently, `J : Type wj` carries `Category.{vj} J`; neither
its object universe `wj` nor its hom universe `vj` is tied to `u` or `w`.
There is no filteredness condition on `J`, `HasWeakSheafify` assumption, or
assumption that sheaf colimits exist globally. The conclusion concerns the
given cocone, not sheaf-colimit existence, reflection or creation of native
limits by the underlying-space functor, or any registered global instance.

## Proof mechanism

For **any** competing cocone `K` over the inverse-image sheaf diagram of the
actual forgotten cone, form the native cone
`Q := coneOfPullbackCocone A S ((forget A).mapCone C) K`.
Its vertex has the original base space, and its projections have the original
base maps. The native limit gives `m := hC.lift Q` and its actual projection
triangles. Applying `hbase.hom_ext` to their base components proves
`m.hom.base = 𝟙 (C.pt : TopCat)`; the proof eliminates this equality before
building the sheaf-map descent rather than treating unequal base arrows as
definitionally equal.

The inverse-image mate of identity-base `m` starts at the pullback of
`C.pt.sheaf` along the identity. Precompose with `pullbackIdInv` to obtain
`C.pt.sheaf ⟶ K.pt`. The private identity-first normalization proves
`triangleMap A (Category.id_comp p) a ≫ pullbackIdHom A X G = a` using
`pullbackCompIso_comp_id` and `pullbackIdHom_naturality`. Cancelling the
identity-pullback comparison turns the native projection triangles into the
competing cocone's leg equations. This identity-first law differs from the
inherited `triangleMap_id`, which has the identity in the other position.

For uniqueness, a rival `d : C.pt.sheaf ⟶ K.pt` satisfying all the leg
equations defines an identity-base native arrow `Q.pt ⟶ C.pt`, whose mate is
`pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫ d`. The adjunction supplies its
component; identity-first normalization and `sheafMate_triangle_converse`
prove its native projection triangles. Native-limit uniqueness identifies
this arrow with `m`, and cancellation of the invertible `pullbackIdHom`
identifies `d` with the constructed descent. No desired `IsColimit` witness
is assumed.

## Import-only clients and boundary

`SheafCohomologyExamples.ConePullbackLimitConverse` imports the producer and
tests the iff with independent category and shape universes. Its named
declarations are private import-only checks, not additional public API.
For arbitrary `Type v` and `AddCommGrpCat.{v}` diagrams indexed by `Fin 3`,
the clients take genuine base/native limit witnesses and **arbitrary supplied**
sheaf cocones. They test factorization, uniqueness, and the composite of the
nonidentity **index arrows** `0 ⟶ 1` and `1 ⟶ 2`; their diagram images need
not themselves be nonidentity.

For the empty index shape, the client constructs the actual forgotten base
cone's limit witness from `TopCat.isTerminalPUnit`. It **separately requires**
a genuine native `IsLimit` for the actual empty native cone, then obtains the
canonical sheaf `IsColimit`. It neither assumes the conclusion nor proves
that an arbitrary chosen empty native cone is limiting. Compare the distinct
[limit construction](SheafedSpaceLimitConstruction.md), which has additional
existence assumptions not used here.
