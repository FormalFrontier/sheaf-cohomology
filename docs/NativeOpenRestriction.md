# Native restriction to inverse-image opens

Import `SheafCohomology.NativeOpenRestriction` for the public API in
`AlgebraicGeometry.SheafedSpace`. Its coefficient category is
`{C : Type (v + 1)} [Category.{v} C]`, and its objects are
`SheafedSpace.{v + 1, v, v} C`. The base-space and coefficient category use the
same universe `v`. There is no requirement of points, a nonempty space or open,
extra limits, or a concrete coefficient category. Setting `C = Type v` gives
the **same** declarations as the original Type-valued API, with no renaming or
parallel implementation. The existing ordinary-import Type example
`SheafCohomologyExamples.NativeOpenRestriction` remains unchanged;
`C = AddCommGrpCat.{v}` is another specialization.

Given `g : X ⟶ Y` and `V : Opens Y`, define the source open *exactly* by
`U := (Opens.map g.hom.base).obj V`. The native arrow
`restrictOnPreimage g V` has type

```lean
X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding
```

It is induced by mathlib's `PresheafedSpace.IsOpenImmersion.lift` of the
**existing** open immersion `Y.ofRestrict V.isOpenEmbedding` along
`X.ofRestrict U.isOpenEmbedding ≫ g`, not by constructing a second sheaf or
base-change map. `restrictOnPreimage_range` supplies the inverse-image range
witness. `restrictOnPreimage_fac` states the commuting inclusion square as an
equality of **full sheafed-space arrows**, and `restrictOnPreimage_unique`
characterizes the arrow by that same full-arrow square via the open-immersion
`lift_uniq`. `restrictOnPreimage_base` identifies its literal underlying
continuous map with the official
`TopCat.Sheaf.OpenBaseChange.preimageMap g.hom.base V`.

For an independently named `U' : Opens X` and proof
`h : U' = (Opens.map g.hom.base).obj V`, use
`restrictOnNamedPreimage g V U' h`. Its inclusion square
`restrictOnNamedPreimage_fac` uses that equality rather than treating the
opens as definitionally equal. `restrictOnNamedPreimage_id` proves identity
after the `Opens.map_id_obj` cast; `restrictOnPreimage_comp` proves composition
after the `Opens.map_comp_obj` cast, using the monic *native restriction*
inclusions. The composition source is `(Opens.map (f ≫ g).hom.base).obj W`,
transported to the iterated inverse image
`(Opens.map f.hom.base).obj ((Opens.map g.hom.base).obj W)`.

`restrict_Γ_obj X U` identifies global sections of the native restriction
with `X.presheaf.obj (op U)` using `Opens.isOpenEmbedding_obj_top`.
`ofRestrict_c_app_self` identifies the inclusion's component on that open.
With **both** explicit `eqToHom` transports, `restrictOnPreimage_Γ_map`
identifies `Γ.map (restrictOnPreimage g V).op` with the original component
`g.hom.c.app (op V)`. `restrictOnNamedPreimage_Γ_map` also transports from
the canonical inverse-image open to `U'`, using `h.symm` in the
presheaf-object cast. The proof uses the full-arrow square, the actual
presheaf morphism's naturality and cancellation of an equality transport:
`TopCat.Presheaf.pushforward C` maps an `eqToHom` to an isomorphism, hence a
monomorphism for arbitrary `C`. It uses no Type-element injectivity or
assumed component equality.

The existing ordinary-import **Type** example composes two genuine native
arrows and recovers the original composite component with its nondefinitional
`Opens.map_comp_obj` cast. The separate ordinary-import **additive** example
`SheafCohomologyExamples.NativeOpenRestrictionAdditive` checks the same
readback for composable `AddCommGrpCat` arrows. Its *named private* theorem
`composed_sections_readback` retains the explicit cast and proof; it neither
creates a public theorem nor assumes its desired equality. The example root imports the additive private client; the public root
imports the same category-generic producer.

## Boundaries and verification

This module alone does **not** construct principal-tail functors, restricted cylinder
cones or limits, native-limit comparisons, colimit-leg naturality, spectral
transport or the additive compact-cylinder endpoint. Preservation of a limit
by coefficient forgetting does not imply reflection of an additive limit.
No source-level correspondence or coverage decision follows from this unit.

See the [cylinder guide](NativeCylinderLimit.md) for the separate
restricted-cone limit construction and the
[open-naturality guide](NativeCylinderOpenNaturality.md) for later
open-variable comparisons. The open-immersion lift adapted here is
Andrew Yang's Apache-2.0 mathlib work; see [credits](CREDITS.md).
