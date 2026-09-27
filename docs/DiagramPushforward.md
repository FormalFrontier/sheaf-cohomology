# Varying-base diagram pushforward of sheafed spaces

Import `SheafCohomology.DiagramPushforward` for native
`AlgebraicGeometry.SheafedSpace.diagramPushforward` and
`AlgebraicGeometry.SheafedSpace.diagramPushforwardCone`. Neither constructor
requires a limit, an invertible stage map, or a Cartesian square.

## Diagram and variance

Let `J` be any category, `N : Jᵒᵖ ⥤ SheafedSpace A`,
`Y : Jᵒᵖ ⥤ TopCat` and
`f : N ⋙ SheafedSpace.forget A ⟶ Y`. The new diagram has space `Y.obj i`
and sheaf `(TopCat.Sheaf.pushforward A (f.app i)).obj (N.obj i).sheaf`.
For `a : i ⟶ j` **in `Jᵒᵖ`**, set `p := (N.map a).hom.base` and
`q := Y.map a`; thus in the original category a stage arrow `j ⟶ i`
becomes a map from the sheafed stage over `j` to the one over `i`.
Naturality supplies the actual strict square
`p ≫ f.app j = f.app i ≫ q`. Its arrow over `q` has sheaf map

```lean
(TopCat.Sheaf.pushforward A (f.app j)).map
    (⟨(N.map a).hom.c⟩ : (N.obj j).sheaf ⟶
      (TopCat.Sheaf.pushforward A p).obj (N.obj i).sheaf) ≫
  (TopCat.Sheaf.SquareTransition.pushforwardSquareIso A
    p q (f.app j) (f.app i) (diagramPushforward_square A N Y f a)).hom.app
      (N.obj i).sheaf
```

The strict comparison points *forward*, from pushforward along `p ≫ f.app j`
to pushforward along `f.app i ≫ q`. The square need not be Cartesian.
`diagramPushforward_map_sheafMap` and `diagramPushforward_map_mate`
give the precise map and its native inverse-image mate; the latter is
`SquareTransition.transition A p q (f.app j) (f.app i) square
  (SheafedSpace.sheafMate A (N.map a))`.
`diagramPushforwardHom_id` and `diagramPushforwardHom_comp` establish the
native functor laws from the strict square (including its proof-irrelevant
equality transport); these laws are not extra assumptions on the target diagram.

The public stage API is `diagramPushforwardObj` with
`diagramPushforwardObj_carrier`/`diagramPushforwardObj_sheaf`, and
`diagramPushforwardHom` with `diagramPushforwardHom_base`,
`diagramPushforwardHom_sheafMap`, `diagramPushforwardHom_mate`,
`diagramPushforwardHom_id` and `diagramPushforwardHom_comp`. At the diagram
level, `diagramPushforward_square` supplies the naturality equality,
`diagramPushforwardMap` its map with `_id`/`_comp` laws, and
`diagramPushforward` the native functor. Its equations are
`diagramPushforward_obj`, `diagramPushforward_map`,
`diagramPushforward_obj_carrier`, `diagramPushforward_obj_sheaf`,
`diagramPushforward_map_base`, `diagramPushforward_map_sheafMap` and
`diagramPushforward_map_mate` (all in `AlgebraicGeometry.SheafedSpace`).

## Compatible cones

Given native `c : Cone N`, native `d : Cone Y`, a continuous
`g : (c.pt : TopCat) ⟶ d.pt`, and the actual projection compatibility
`∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i`, use
`diagramPushforwardCone A N Y f c d g h`. Its vertex has space `d.pt`
and sheaf `(TopCat.Sheaf.pushforward A g).obj c.pt.sheaf`; its projection
at `i` lies over `d.π.app i` and is the pushforward of the source
projection's sheaf map followed by the forward comparison for the
projection square. `diagramPushforwardCone_projection_sheafMap` and
`diagramPushforwardCone_projection_mate` compute that projection and
its mate (the transition of `sheafMate A (c.π.app i)`). The cone law uses
`c.w`, `d.w`, naturality of `f`, and strict square pasting. No limit or
colimit property for either cone is asserted.
The public cone equations are `diagramPushforwardCone_pt`,
`diagramPushforwardCone_projection`, `diagramPushforwardCone_carrier`,
`diagramPushforwardCone_sheaf`, `diagramPushforwardCone_projection_base`,
`diagramPushforwardCone_projection_sheafMap`, and
`diagramPushforwardCone_projection_mate`.

## Assumptions and examples

The native diagram and cone constructors need only `Category.{w} A`;
`A : Type u`, the spaces are `TopCat.{w}`, and `J : Type wj` has
`Category.{vj} J`. There is no size or nonemptiness restriction on `J`.
The *mate characterizations* additionally need the same concrete-category,
limits, colimits, preservation, and isomorphism-reflection instances as
`TopCat.Sheaf.pullbackPushforwardAdjunction`: concrete carrier and space
universes both equal `w`, while coefficient object and index universes
remain independent. These are requirements for native pullback/mate APIs,
not existence assumptions for the direct-image constructors.

For elaborated arbitrary `Fin 3` nonidentity arrows, actual source/target cones
and projection mates with both `Type v` and `AddCommGrpCat.{v}` coefficients,
import `SheafCohomologyExamples.DiagramPushforward`. Its private clients check
the stage base map, additive sheaf map, Type-valued mate, two-arrow composition,
native cone projection mate and additive cone law. It also constructs genuine
empty-index native cones with an arbitrary map of their vertices; no client
statement asserts a cone is limiting. These clients introduce no public API.
No coefficient-changing or ringed/scalar structure is supplied. This is
not an endpoint-isomorphism, a limit-existence statement, or a claim about
source coverage.

The `SheafCohomology` aggregate root re-exports this module, and
`SheafCohomologyExamples` imports its private clients. Exact combined review,
acceptance and release are separate from this registration. The original incubator mathematical
candidate was authored by worker-b Hive Task
`hive-request-3628aceedd705e9f2a33087597c31b7244ce8eae`, UID
`5d89eac6-5b60-41a0-bb24-b0c348237cd7`, at
`6c81996064d5679c45aac8864c8269a4e6795383` and independently reviewed at
`5308a6f7f5d1f8e49b239b4e71cf6913890697f1`. Destination transfer by
worker-a Hive Task `hive-request-2be4e9b76c87d5c099ccb8d23c1ed738e7063fdc`,
UID `47ed4e53-94f9-4a23-b8e6-db812145fea9`, onto exact destination base
`15c2e06a74e423728bbc745429325d8bdfc65b95`.
