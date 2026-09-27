# Coefficient forgetting and native diagram pushforward

Import `SheafCohomology.AbelianForget.DiagramPushforward`. This
module compares direct images of genuine diagrams of abelian-group-valued
sheafed spaces with direct images after forgetting the additive structure.
The comparison does not construct a different diagram, alter the topological
spaces, or assume that a naturality square is Cartesian.

## Diagram and arrows

Let `J : Type wj` carry `Category.{vj} J`. Let
`N : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}`,
`Y : Jᵒᵖ ⥤ TopCat.{v}`, and
`f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y`.
`underlyingDiagram_forget` and `underlying_forget` say that the same `f`
also has the Type-valued domain `(N ⋙ underlying) ⋙ SheafedSpace.forget
(Type v)` by *literal* equality. The public theorem
`underlying_diagramPushforward N Y f` identifies the two functors by equality:

```lean
SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f ⋙ underlying =
  SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f
```

At `i : Jᵒᵖ`, both objects have carrier `Y.obj i` and Type-valued sheaf
`(TopCat.Sheaf.pushforward (Type v) (f.app i)).obj
  ((underlyingSheaf (N.obj i : TopCat)).obj (N.obj i).sheaf)`.
The object equality is `underlying_diagramPushforwardObj`; carrier and sheaf
formulas are `underlying_diagramPushforward_obj_carrier` and
`underlying_diagramPushforward_obj_sheaf`.

For an **actual** `a : i ⟶ j` in `Jᵒᵖ`, the underlying arrow lies over
`Y.map a` (`underlying_diagramPushforward_map_base`). Its whole morphism
agrees with the Type-valued native arrow
(`underlying_diagramPushforward_map`). The formula for its underlying sheaf
map (`underlying_diagramPushforward_map_sheafMap`) is

```lean
(TopCat.Sheaf.pushforward (Type v) (f.app j)).map
    ((underlyingSheaf (N.obj j : TopCat)).map
      (⟨(N.map a).hom.c⟩ : (N.obj j).sheaf ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
          (N.map a).hom.base).obj (N.obj i).sheaf)) ≫
  (TopCat.Sheaf.SquareTransition.pushforwardSquareIso (Type v)
    (N.map a).hom.base (Y.map a) (f.app j) (f.app i)
    (SheafedSpace.diagramPushforward_square AddCommGrpCat.{v} N Y f a)).hom.app
      ((underlyingSheaf (N.obj i : TopCat)).obj (N.obj i).sheaf)
```

The square proof is the actual naturality of `f`. The substantive arrow
comparison uses the already established strict `underlyingSheaf_pushforward_map`
and `underlyingSheaf_pushforwardSquareIso_hom_app`, including its equality
transport; it does not assert square compatibility as a hypothesis. For mates,
`underlying_diagramPushforward_map_mate` follows directly from the established
`underlying_sheafMate` at the actual pushed stage arrow. The existing
`canonicalComponent_transition` gives the corresponding transition formula;
no new mate or transition calculus is needed.

The sixteen declarations in the public API, all in
`AlgebraicGeometry.SheafedSpace.AbelianForget`, are:

- Objects and diagrams: `underlying_diagramPushforwardObj`,
  `underlying_diagramPushforward`, `underlying_diagramPushforward_obj_carrier`,
  `underlying_diagramPushforward_obj_sheaf`.
- Arrows: `underlying_diagramPushforwardHom`,
  `underlying_diagramPushforward_map`, `underlying_diagramPushforward_map_base`,
  `underlying_diagramPushforward_map_sheafMap`,
  `underlying_diagramPushforward_map_mate`.
- Cones: `underlying_diagramPushforwardConeIso`,
  `underlying_diagramPushforwardCone_vertex`,
  `underlying_diagramPushforwardCone_carrier`,
  `underlying_diagramPushforwardCone_sheaf`,
  `underlying_diagramPushforwardCone_projection`,
  `underlying_diagramPushforwardCone_projection_base`,
  `underlying_diagramPushforwardConeIso_hom`.

## Compatible cones

Given `c : Cone N`, `d : Cone Y`, **any** continuous vertex map
`g : (c.pt : TopCat) ⟶ d.pt`, and the actual projection-square hypotheses
`h i : (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i`, use
`underlying_diagramPushforwardConeIso N Y f c d g h`. Its source is the native
`underlying.mapCone` of `diagramPushforwardCone AddCommGrpCat`, postcomposed by
`Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))`; its target
is `diagramPushforwardCone (Type v) (N ⋙ underlying) Y f
  (underlying.mapCone c) d g h`. Thus both are cones over the **same** target
diagram, with no replacement cone record. The iso has identity vertex map
(`underlying_diagramPushforwardConeIso_hom`).

The compared vertex has carrier `d.pt` and sheaf
`(TopCat.Sheaf.pushforward (Type v) g).obj
  ((underlyingSheaf (c.pt : TopCat)).obj c.pt.sheaf)`; see the
`underlying_diagramPushforwardCone_vertex`, `_carrier`, and `_sheaf`
theorems. After the diagram equality transport, its actual projection at
`i : Jᵒᵖ` **equals** the Type-valued native pushed projection
(`underlying_diagramPushforwardCone_projection`), and its base is `d.π.app i`
(`underlying_diagramPushforwardCone_projection_base`). To expand that
projection's sheaf map and mate, use the existing
`diagramPushforwardCone_projection_sheafMap` and `_mate` on the Type-valued
cone, respectively; they apply to arbitrary `g` and the actual `h i`.

## Bounds and testing

The shared universe `v` for `TopCat.{v}`, `AddCommGrpCat.{v}`, and `Type v`
matches native sheaf-composition and direct-image APIs. The small indexing
category `J : Type wj` has arbitrary morphism universe `vj`; no relationship
between its universes and `v`, nonemptiness, (co)filteredness, limit property,
isomorphism of stage maps, or special property of the vertex map is assumed.
All definitions are noncomputable in the native sheafed-space setting.

The public-import-only module
`SheafCohomologyExamples.AbelianForgetDiagramPushforward` contains twelve
private clients. They exercise
both nonidentity `Fin 3` arrows, their genuine composition, compatible
projections of arbitrary native cones, and empty-index native cones. Both
the production and client modules are registered in the default project
roots in this destination candidate. Exact independent destination/release
review, owner acceptance and verified publication remain separate steps.
These are reusable compatibility results, not source correspondence, a limit
theorem, a ringed-space construction, or an assertion of source coverage.

Author: Hive Task `hive-request-620e7673c746798330d114e0e2debbc4a80a2381`,
UID `41fde94b-1957-44b7-9437-430fe5cfd02b` (worker-a).
Destination transfer: Hive Task `hive-request-0ad06f8848e144e0c34ccd44ac71e2da46c56d58`,
UID `520ced02-de5d-483f-b69f-e8bfb284babe` (worker-a).
The source leaf was reviewed at incubator commit
`d30bbc667d43143d8c4ecda7c4e8ba3ca3125508`; its production, example and
guide blobs are `6600ab7a29876aacc9d6f06c4bcd42a879f3d1ad`,
`008fca3b697a09d0a74ea17aaa1620892d930ddb`, and
`18284d7fc00d46fae8a54c0f92735a025f1d67c0`, respectively. The
original was independently reviewed by Hive Task
`hive-request-8be7926df253d0f7e3ad3250be1aa1e60aa3a73f`, UID
`90252b07-2de0-4ffa-9cd2-2b370241b64a` (worker-b), at review record
`d307da4ce3d178104b770e0ffa342f9b14251605`. The destination project
retains its Apache-2.0 license.
