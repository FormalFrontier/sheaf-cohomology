# Open naturality of native cylinder sections

Import `SheafCohomology.NativeCylinderOpenNaturality`, or the aggregate
`SheafCohomology` root. This module extends the
[native open-restriction](NativeOpenRestriction.md) and
[cylinder](NativeCylinderLimit.md) APIs of
`SheafCohomology.NativeOpenRestriction` and
`SheafCohomology.NativeCylinderLimit`, together with the existing pointwise
`SheafCohomology.NativeCommRingCylinderSections` and
`SheafCohomology.NativeAdditiveCylinderSections` comparisons. The
ordinary-import example is `SheafCohomologyExamples.NativeCylinderOpenNaturality`.
See also the separate
[ring](NativeCommRingCylinderSections.md) and
[additive](NativeAdditiveCylinderSections.md) pointwise cylinder guides.

All names below are in
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`. Fix one universe `v`, a
coefficient category `C : Type (v + 1)` with `[Category.{v} C]`, a preorder
`ι : Type v` with `[IsDirectedOrder ι]`, a diagram
`S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C`, a base stage `i0 : ι`, and **any**
original cone `m : Cone S`. No limiting-cone hypothesis is assumed. Set
`Xᵢ := S.obj (op i.1)` for `i : Set.Ici i0`, and let
`Wᵢ := stageOpen S i0 W i` and `Wₘ := coneOpen S i0 m W` for an open
`W : Opens (S.obj (op i0))`.

## Restricted-stage diagrams and open maps

`cylinderSections S i0 W` is the *actual* stage diagram

```lean
(restricted S i0 W).rightOp ⋙ SheafedSpace.Γ : Set.Ici i0 ⥤ C
```

For `h : U ≤ V`, `stageOpen_mono S i0 h i` proves `Uᵢ ≤ Vᵢ`, and
`stageSectionRestriction S i0 U V h i` has type
`(cylinderSections S i0 V).obj i ⟶ (cylinderSections S i0 U).obj i`.
It is **the original presheaf's restriction** with both necessary transports:

```text
eqToHom (SheafedSpace.restrict_Γ_obj Xᵢ Vᵢ)
  ≫ Xᵢ.presheaf.map (homOfLE (stageOpen_mono S i0 h i)).op
  ≫ eqToHom (SheafedSpace.restrict_Γ_obj Xᵢ Uᵢ).symm
```

`stageSectionsRestriction S i0 U V h : cylinderSections S i0 V ⟶
cylinderSections S i0 U` is a **natural transformation**, not just a list of
stage arrows. Its naturality uses the original transition's presheaf-morphism
naturality and the named inverse-image equality. The theorems
`stageSectionsRestriction_id` and `stageSectionsRestriction_comp` state open
identity and composition; no compactness or nonempty-open condition is needed.

## Colimit presheaf and comparison

For the open-variable presheaf, supply

```lean
[∀ W : Opens (S.obj (op i0)), HasColimit (cylinderSections S i0 W)]
```

These are the colimits used by this particular family, not a blanket
cocompleteness assumption. `cylinderSectionsPresheaf S i0` is a functor from
`(Opens (S.obj (op i0)))ᵒᵖ` to `C`, with object `colimit
(cylinderSections S i0 W)` and restriction `colimMap
(stageSectionsRestriction S i0 U V h)` for `h : U ≤ V`. Its identity and
composition use the corresponding stage-transformation laws and the colimit
coprojection universal property.

`cylinderSectionsComparison S i0 m W` maps this colimit to
`m.pt.presheaf.obj (op Wₘ)`. Its cocone has stage leg

```text
SheafedSpace.Γ.map ((restrictedCone S i0 m W).π.app (op i)).op
  ≫ eqToHom (SheafedSpace.restrict_Γ_obj m.pt Wₘ).
```

The leg is `colimit_ι_cylinderSectionsComparison`. The theorem
`originalStage_cylinderSectionsComparison` gives the more useful **original**
projection formula: precompose its leg by
`eqToHom (SheafedSpace.restrict_Γ_obj Xᵢ Wᵢ).symm`; the result is
`(m.π.app (op i.1)).hom.c.app (op Wᵢ)` followed by the *reverse* cast
`eqToHom (congrArg (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
  (coneOpen_eq_stage S i0 m W i).symm)`.

For `h : U ≤ V`, `coneOpen_mono S i0 m h : Uₘ ≤ Vₘ`. The actual
commuting square is `cylinderSectionsComparison_restrict`:

```text
colimMap (stageSectionsRestriction S i0 U V h)
    ≫ cylinderSectionsComparison S i0 m U
  = cylinderSectionsComparison S i0 m V
    ≫ m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h)).op.
```

`cylinderSectionsNaturality S i0 m` packages this square as a natural
transformation to the **literal** target
`(Opens.map (m.π.app (op i0)).hom.base).op ⋙ m.pt.presheaf`. Its component
is the generic comparison followed by the object cast induced by
`coneOpen_base S i0 m W`; the cast is needed because `coneOpen` is a named,
non-definitional inverse image.

## Ring and additive usage

For `C = CommRingCat.{v}` or `C = AddCommGrpCat.{v}`, the existing small
colimits provide the family above. `ringCylinderSectionsComparison_eq` and
`additiveCylinderSectionsComparison_eq` identify the corresponding *official*
pointwise cylinder comparisons with the generic arrow via their actual
coprojection-leg laws. Their open squares are
`ringCylinderSectionsComparison_restrict` and
`additiveCylinderSectionsComparison_restrict`; these are consequences of the
one generic construction, not separate comparison engines.

For a stage ring section `a : Xᵢ.presheaf.obj (op Vᵢ)`, form a named section
over `Vₘ` by applying the original projection component and then the reverse
`coneOpen_eq_stage` transport. The private example
`SheafCohomologyExamples.NativeCylinderOpenNaturality.ringStageRepresentativeRestriction`
checks that restricting this named section to `Uₘ` agrees with sending the
stage representative through `eqToHom (restrict_Γ_obj Xᵢ Vᵢ).symm`, its
colimit coprojection, `colimMap (stageSectionsRestriction S i0 U V h)`, and
the official comparison at `U`. The same client tests an additive original
projection, a strict open inclusion when one is supplied, the empty open,
and stage restriction composition and identity. No synthetic geometric space
or strictness assumption appears in the producer.

To build only the two modules from the pinned project root, first obtain the
matching cache and then run:

```sh
lake exe cache get
lake build SheafCohomology.NativeCylinderOpenNaturality
lake build SheafCohomologyExamples.NativeCylinderOpenNaturality
```

These are **arrow** laws. Invertibility remains conditional on the separate
spectral/compact-open/limiting-cone theorems; nothing here constructs a
natural isomorphism on all opens, a chosen-limit bridge, stalks, a sheaf
reconstruction, or a scheme structure. All types use the same-universe native
sheafed-space API.
