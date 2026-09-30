# Additive sections of a native compact-open cylinder

Import `SheafCohomology.NativeAdditiveCylinderSections` to use the
actual-cone comparison. Fix a directed preorder `ι : Type v`,
`S : ιᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v}`, an index `i0 : ι`,
an **arbitrary** original native cone `m : Cone S`, and an open
`U0 : Opens (S.obj (op i0))`. The comparison definition and both
projection laws need only `[Preorder ι]`; directedness is used for the
IsIso theorem, not smuggled into the ordinary colimit construction.
Write
`R := NativeCylinderLimit.restricted S i0 U0` and
`mR := NativeCylinderLimit.restrictedCone S i0 m U0`.

For varying stage opens, the
[generic cylinder open-naturality guide](NativeCylinderOpenNaturality.md)
identifies this same additive comparison with the generic arbitrary-original-cone
arrow and derives its restriction square from the actual restricted-stage
transformation. That arrow law requires no limiting cone, spectrality or
compact-open assumption; the pointwise `IsIso` result below retains its
separate hypotheses.

`NativeCylinderLimit.nativeAdditiveCylinderSectionsComparison S i0 m U0`
is an additive morphism

```lean
colimit (R.rightOp ⋙ SheafedSpace.Γ) ⟶
  m.pt.presheaf.obj (op (NativeCylinderLimit.coneOpen S i0 m U0))
```

for **any** `m`; no `IsLimit`, spectral, compactness, surjectivity or
nonempty-space assumption enters its definition or its arrow laws. The
codomain is sections of the **original** cone point over the inverse image
of `U0` under the original projection at `i0`, not sections of a chosen
replacement limit. The comparison first uses the existing
`SheafedSpace.nativeAdditiveGlobalSectionsComparison R mR` on the actual
restricted diagram and cone, then the *forward* transport
`eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))` from
global sections of the literal restricted cone point to the original open.
`mR.pt` is literally the restriction of `m.pt` to that open.

The restricted coprojection law
`NativeCylinderLimit.colimit_ι_nativeAdditiveCylinderSectionsComparison`
identifies each colimit leg followed by the comparison with the actual
`Γ.map (mR.π.app (op i)).op` followed by that forward transport. The
**original-stage** law
`NativeCylinderLimit.originalStage_nativeAdditiveCylinderSectionsComparison`
is an equality of `AddCommGrpCat` morphisms, not merely carrier functions:

```lean
eqToHom (SheafedSpace.restrict_Γ_obj
    (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
  colimit.ι (R.rightOp ⋙ SheafedSpace.Γ) i ≫
    nativeAdditiveCylinderSectionsComparison S i0 m U0 =
  (m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
    eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
      (coneOpen_eq_stage S i0 m U0 i).symm)
```

The left `.symm` moves original stage-open sections into Γ of the
**literal** restricted stage. The right `.symm` moves the projection's
preimage-open sections back to sections on the named `coneOpen` in `m.pt`.
The proof applies the generic `restrictOnNamedPreimage_Γ_map` to the
actual original projection and identifies the native cone component by
its monic open-inclusion square. It does not use an assumed Γ-forgetting
bridge, a chosen-limit comparison, or a carrier-only equality.

If `hm : IsLimit m`, every original stage of
`S ⋙ SheafedSpace.forget AddCommGrpCat.{v}` is spectral, every original
transition is spectral, and `U0` is compact (including the empty open),
`NativeCylinderLimit.isIso_nativeAdditiveCylinderSectionsComparison`
proves this comparison is an isomorphism. The generic
principal-tail filteredness needed **only inside this proof** is supplied
locally: `i0` inhabits the tail, `tailDirectedOrder i0` supplies
directedness, and mathlib infers `IsFiltered (Set.Ici i0)`.
No global tail instance or linear order is added. The generic
`restrictedIsLimit S i0 m hm U0` **constructs** the required native
restricted-cone limit. The separate reusable generic module
`SheafCohomology.NativeSpectralCylinder` proves spectrality
of the actual restricted stages and maps for any coefficient category
`C : Type (v+1)` with `[Category.{v} C]`, directly from the original
spectral system and compact `U0`, with *no cone or limit assumptions*.
Its topology proof occurs only once: `spectralStage` transports compactness
along original transitions and uses the compact-open embedding;
`spectralStageMap` uses retrocompactness of the original open, the actual
native `stageMap_fac` square and the published spectral-subspace criterion.
The additive global comparison applies to the constructed
restricted limit and these spectral hypotheses. Composing its isomorphism
with the forward `eqToHom` proves the endpoint without assuming the result.
The original Type-valued chosen-limit endpoint still uses this shared
helper at `C := Type v`, with its original public conclusion unchanged.

An ordinary importer,
`SheafCohomologyExamples.NativeAdditiveCylinderSections`, contains
the **named private**
`originalStage_detects_transported_coprojection_additive`: equality of
two sections under the *actual original projection* and the right-hand
named-open cast implies equality after the left-hand restriction-object
transport and actual colimit coprojection. It uses this proved `IsIso`,
`forget AddCommGrpCat` and concrete injectivity, and the original-stage
arrow law. Neither desired equality nor injectivity is assumed. Empty
opens and spaces are not excluded. The client is a usage check, not a
source-correspondence claim.
