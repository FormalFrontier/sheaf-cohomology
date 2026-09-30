# Native sheafed-space limits from pullback-sheaf colimits

Import `SheafCohomology.ConePullbackLimit`. For an arbitrary
`S : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace A` and an **actual** native
`C : Cone S`, the primary result is

```text
SheafedSpace.isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone A S C
  (hbase : IsLimit ((SheafedSpace.forget A).mapCone C))
  (hsheaf : IsColimit (SheafedSpace.conePullbackCocone A S C)) : IsLimit C
```

These are universal properties of the *actual* forgotten cone and the
*actual* projection-mate sheaf cocone. They are not a limit assumption about
`C`, a stipulated comparison isomorphism, or a stipulated lift. In particular
there is no assumption that `J` is filtered, inhabited, spectral, Cartesian,
or small relative to the sheaf universe. `J : Type wj` carries
`Category.{vj} J`, with `wj` and `vj` independent of each other and of the
coefficient and topological-space universes. Coefficients satisfy precisely
the existing `ConePullback` hypotheses: `A : Type u`, `Category.{w} A`,
`FunLike` and `ConcreteCategory.{w}` with concrete carrier in `Type w`,
`HasLimits A`, `HasColimits A`, and preservation of limits and filtered
colimits and reflection of isomorphisms by `CategoryTheory.forget A`.

## Actual lift and base change

For a competing native cone `Q : Cone S`, put `c = (forget A).mapCone C`,
`q = (forget A).mapCone Q`, and `f = hbase.lift q`. The equations
`hbase.fac q i : f ≫ c.π.app i = q.π.app i` hold for **every** index object.
The public `conePullbackBaseChangeIso A S c q f (hbase.fac q)` identifies

```text
conePullback A S c ⋙ TopCat.Sheaf.pullback A f ≅ conePullback A S q.
```

It is not an assumed isomorphism. Its stage component is the canonical
`TopCat.Sheaf.pullbackCompIso A f (c.π.app (op i))`, followed by the *proved*
equality of complete projection natural transformations. Naturality uses
`triangleMap_baseChange`, derived from the associativity and naturality of
`pullbackCompIso`, the real index-arrow mates, and both cone triangles.
The narrow public `pullbackCompInv_assoc` in `ConePullback` exports the
predecessor's unchanged private associativity proof, so this module does
not duplicate its proof body; the import-only client exercises that public
component law directly.
`conePullbackBaseChangeIso_triangle` states that its component followed by
the transported pullback of any stage map `m` equals `f^*.map m`; this
explicitly cancels the composition comparison and its inverse. It does not
silently identify pullbacks along unequal base arrows.

Transporting Q's projection-mate cocone across this comparison gives the
actual `conePullbackLimitTargetCocone A S C hbase Q` over the diagram
`conePullback A S c ⋙ f^*`. The functor `f^*` is a left adjoint to
pushforward, so `isColimitOfPreserves (TopCat.Sheaf.pullback A f) hsheaf`
applies to the **supplied** colimiting cocone. Its `desc` into that competing
cocone is `conePullbackLimitSheafMap A S C hbase hsheaf Q :
f^*(C.pt.sheaf) ⟶ Q.pt.sheaf`. The adjunction mate of this map, paired
with the concrete base `f`, is the native arrow
`conePullbackLimitLift A S C hbase hsheaf Q : Q.pt ⟶ C.pt`.
`conePullbackLimitLift_base` and `_mate` expose both pieces; the definition
does not replace the given cone or its projections.

The colimit factorization says
`f^*.map (sheafMate A (C.π.app (op i))) ≫ desc =
comparison.hom.app i ≫ sheafMate A (Q.π.app (op i))`.
Precomposition with the component comparison and the triangle cancellation
turn this into the equation of inverse-image mates in
`conePullbackLimitSheafMap_fac`. Together with `hbase.fac`,
`sheafMate_triangle_converse` proves the factorization by the **actual native
projection** `C.π.app (op i)`. For uniqueness, `hbase.uniq` first forces the
base of any rival native arrow to be `f`. The real native projection triangles
then give equal component equations after pullback along `f`; the mapped
colimit's `hom_ext` forces equality of inverse-image sheaf mates. Finally
`sheafMate_ext` uses the adjunction and `PresheafedSpace.hext` to turn that
base-and-mate equality into equality of native arrows. In particular, the
private map proof for a fixed base does not rely on an invented uniqueness
hypothesis.

## Explicit reconstruction

For a given *actual* `c : Cone (S ⋙ SheafedSpace.forget A)` and
`K : Cocone (SheafedSpace.conePullback A S c)`, the result

```text
SheafedSpace.coneOfPullbackCoconeIsLimit A S c K
  (hc : IsLimit c) (hK : IsColimit K) :
    IsLimit (SheafedSpace.coneOfPullbackCocone A S c K)
```

uses the previous criterion, the predecessor's **literal whole-cone**
`coneOfPullbackCocone_forget` equality, and the predecessor's **transported**
`conePullbackCocone_coneOfPullbackCocone` equality. Thus `hc` and `hK`
establish the two real hypotheses of the criterion without assuming the
desired native `IsLimit`.

The import-only client `SheafCohomologyExamples.ConePullbackLimit`
instantiates both APIs for arbitrary `Type v` and `AddCommGrpCat.{v}`
diagrams with private declarations, tests the actual native projections,
their inverse-image mates,
both nonidentity arrows `0 ⟶ 1` and `1 ⟶ 2` of `Fin 3`, and their composite.
No assertion that the **images** of those arrows are nonidentity is needed.
The empty-index client separately constructs a diagram over `PEmptyᵒᵖ`,
the actual terminal-space cone with vertex `TopCat.of PUnit`, and its
`IsLimit` using `TopCat.isTerminalPUnit`. It also constructs the actual
empty-index sheaf cocone with an arbitrary specified sheaf vertex. The
conditional client applies the reconstruction theorem to a genuine
`IsColimit` of that cocone, not to an assumed native limit.

At these pins, no `HasColimit`/`HasInitial` instance is synthesized for
`(TopCat.of PUnit.{1}).Sheaf (Type 0)`, even after importing
`Mathlib.CategoryTheory.Sites.Limits`. The exact failure is at the distinct
`TopCat.Sheaf` wrapper (`nonrec def Sheaf ... deriving Category`):
`HasWeakSheafify` *does* synthesize for this topology and `Type 0`, and
`CategoryTheory.Sheaf` *does* have empty-shape colimits, but the corresponding
`HasColimitsOfShape PEmpty (TopCat.Sheaf (Type 0) (TopCat.of PUnit))`
instance does not synthesize. Consequently the
client does **not** claim an explicitly constructed initial sheaf or an
unconditional empty native limit. This is a limitation of the available
native wrapper instance/API at these pins, not a claim that the mathematical
initial sheaf fails to exist. It would be unsound to replace this missing
instance with an assumption of `IsLimit` of the target cone.

There is no generic `HasLimits` instance, arbitrary-large colimit existence
theorem, converse iff, Ringed/scalar extension, source-specific endpoint,
coefficient-forget theorem, or source-coverage claim.
