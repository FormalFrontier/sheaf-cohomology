# Reconstructing a sheafed-space cone from a pullback cocone

Import `SheafCohomology.ConeOfPullbackCocone`. For any
`S : Jᵒᵖ ⥤ SheafedSpace A`, supply an **actual** cone of spaces
`c : Cone (S ⋙ SheafedSpace.forget A)` and an **actual** cocone of sheaves
`K : Cocone (SheafedSpace.conePullback A S c)`. Then

```text
SheafedSpace.coneOfPullbackCocone A S c K : Cone S
```

has vertex `SheafedSpace.pullbackCoconeVertex A S c K`, with carrier *literally*
`c.pt` and sheaf *literally* `K.pt`. The projection at `i : Jᵒᵖ` is
`SheafedSpace.pullbackCoconeLeg A S c K i`. Its base is `c.π.app i`, and
its underlying presheaf map is the map of the adjoint transpose

```text
(TopCat.Sheaf.pullbackPushforwardAdjunction A (c.π.app i)).homEquiv _ _
  (K.ι.app (unop i))
```

The readback declarations are `coneOfPullbackCocone_carrier`, `_sheaf`,
`_π_base`, `_π_c`, and `_π_mate` in `AlgebraicGeometry.SheafedSpace`.
`pullbackCoconeLeg_mate` says that the inverse-image mate of the constructed
projection is **exactly** the supplied cocone leg. The vertex and leg
constructors remain available separately.

## Cone law and transport

For `a : i ⟶ j` in `J`, the stage arrow is
`S.map a.op : S.obj (op j) ⟶ S.obj (op i)`. The base triangle `c.w a.op`
identifies `c.π.app (op j) ≫ (S.map a.op).hom.base` with `c.π.app (op i)`.
The map of `conePullback` on `a` is
`triangleMap A (c.w a.op) (sheafMate A (S.map a.op))`. The actual cocone
law `K.w a` identifies that transition followed by the `j`-leg with the
`i`-leg. Replacing these legs by their exact mates and applying
`sheafMate_triangle_converse` proves the native cone triangle; no native
commutativity was assumed.

The converse requires **both** the equality of the underlying base arrows
and the mate triangle transported along that equality. Its proof uses
`sheafMate_comp`, substitutes the base equality to compare maps with the
same base, then applies the adjunction's hom equivalence and
`PresheafedSpace.hext`/`InducedCategory.hom_ext`. In particular, the
argument does not silently equate inverse images along different base maps:
the equality/heterogeneous-equality step handles that dependent typing.

`coneOfPullbackCocone_forget` is literal equality of the **whole** actual
forgotten cone and `c`, not merely an isomorphism or a vertex comparison.
`conePullbackCocone_coneOfPullbackCocone` recovers the **original** `K` by
transport through precisely that equality:

```text
(coneOfPullbackCocone_forget A S c K) ▸
  conePullbackCocone A S (coneOfPullbackCocone A S c K) = K.
```

The dependent transport makes the two cocone types comparable; its point
and every leg then agree with the supplied ones.

## Assumptions and clients

The coefficient hypotheses are the same as in `SheafCohomology.ConePullback`:
`Category.{w} A`, compatible `FunLike` and `ConcreteCategory.{w} A FA`
data, limits and colimits in `A`, and preservation of limits and filtered
colimits plus reflection of isomorphisms by `CategoryTheory.forget A`.
Coefficient objects have universe `u`; spaces and concrete carriers share
`w`. The index category has independent object and morphism universes
`wj` and `vj`. No nonemptiness, filteredness, topological-limit,
Cartesian-square, stage-isomorphism, or additional index-size assumption
is imposed.

The import-only `SheafCohomologyExamples.ConeOfPullbackCocone` module keeps
all client declarations private. It instantiates arbitrary `Type v` and
`AddCommGrpCat.{v}` diagrams with supplied actual `c` and `K` over `Fin 3`,
exercises both nonidentity **index** arrows and their composite, and checks
the projection mate and forgotten-cone equalities in both categories and
the transported round-trip for `Type v`. Images of those index arrows need
not be nonidentity. For the empty index `PEmpty`, a cocone constructed with
*any* supplied sheaf `F` recovers that sheaf and its forgotten cone.

The library reuses `SheafCohomology.ConePullbackCocone` and the existing
mathlib native sheafed-space/adjunction APIs. It asserts no limiting or
colimiting property, existence of sheafed-space limits, Ringed/scalar or
coefficient-forget result, separate cone framework, source-specific endpoint,
or source-coverage decision.

## Provenance and status

Original mathematical author: Formalization Worker B, Hive Task
`hive-request-fd5f3464b7f33c612645847f878bb0e35e79de1e`, UID
`817007ac-5825-4473-b0be-d3d40a32a445`, incubator PR 71 commit
`b8b80ce57222cdbb98c9d17dfca875ea35518a56` (tree
`1ce1e2ffc1e2d88f443a7151b06d9ae126c2213a`). Its independent
original-content reviewer was distinct Worker A Hive Task
`hive-request-7e2cfb2432e449c2a2434cc35602c601b1d79b77`, UID
`b4ca227c-e275-46b3-bc5f-7f6fe259fbab`, reviewing that exact commit
at review revision `f512ac7814bf22bd67769d549ac90d3e76de6882`.
The responsible maintainer accepted the original content for promotion,
not as a protected-main integration claim. The accepted predecessors retain
their separate credit.

Destination import, client visibility, namespace and guide adaptation:
Formalization Worker A, Hive Task
`hive-request-cbf45ce45ac31f854408fc48bfb3ee338b851bd1`, UID
`8f66d5aa-4564-4c73-92b9-76eb5c62e516`, based on destination main
`069ec1d6d3de9c9f93004057bf785e417eeb45a1`. The exact unregistered leaf
`b7746c1bfd3f1426737b40250cc6b8bf95011b3c` received independent destination
review from Worker B Hive Task
`hive-request-6f6fa2ebcfa5b86d7cc079bbb77d242d91029b2d`, UID
`7ad4e19c-9361-4a9a-a3ab-7c90bf7206b3`, report revision
`2d16286db025851acad0ac4fd335ada44ed158ee`, and owner leaf acceptance.
Anchor preserved both Lean leaves and registered the production and private
client imports on accepted destination
`dff308bf7bd21d1ddcceb2b02c13341685446f22`, with navigation, credit and
scope metadata. This combined candidate still needs applicable combined
checks, exact independent assembly/release review, owner acceptance,
protected integration and verified official publication. None is inferred
from the original or unregistered-leaf approvals.

SPDX-License-Identifier: Apache-2.0
