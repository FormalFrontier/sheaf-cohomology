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
