# Compact-open sections of native spectral cylinders

Import `SheafCohomology.NativeSpectralCylinderSections` for
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit.isIso_restrictedGlobalSectionsComparison`.
This is an isomorphism theorem for the *existing* native comparison, not a new
cylinder or limit construction. The ordinary-import example lives in
`SheafCohomologyExamples.NativeSpectralCylinderSections`.
For the coefficient-generic reusable stage/map results alone, import
`SheafCohomology.NativeSpectralCylinder` instead; it has no chosen-limit
comparison import.

Fix `{ι : Type v} [Preorder ι] [IsDirectedOrder ι]`, `i0 : ι`,
`N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)`, a cone `m : Cone N`
with `hm : IsLimit m`, and `U0 : Opens (N.obj (op i0))`. Its three additional
hypotheses, about the *original* diagram and open, are exactly:

```lean
hstage : ∀ k : ιᵒᵖ,
  SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k)
htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
  IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)
hU0 : IsCompact (U0 : Set (N.obj (op i0)))
```

The conclusion is
`IsIso (restrictedGlobalSectionsComparison N i0 m hm U0)`.
The map's source is
`colimit ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ)` and its target is
`m.pt.presheaf.obj (op (coneOpen N i0 m U0))`. It uses the actual native
`restricted`, `restrictedCone` and `restrictedGlobalSectionsComparison`, with
`hm` referring to the original cone. No spectrality or limit hypothesis for
the restricted diagram, desired isomorphism, surjectivity, nonempty stage/open,
linear order, endpoint, or additive structure is assumed. In particular, `U0`
may be empty: `i0` itself supplies the nonempty directed tail `Set.Ici i0`.

## Proof and ordinary-import client

The spectrality proofs formerly private here are extracted once, with
their original topology-expression credit, to public
`NativeCylinderLimit.spectralStage` and `spectralStageMap` in
`SheafCohomology.NativeSpectralCylinder`. For arbitrary coefficients
`C : Type (v+1)` with `[Category.{v} C]`, they assume only original
spectral stages/maps and compact `U0`; neither a cone, `IsLimit`, directed
tail nor nonempty open is needed. The helper explicitly imports
`Mathlib.Topology.Constructible` and official
`SpectralStoneDuality.Subspace`, not this Type endpoint. Public
`stageOpen_map` and `stageOpen_base` identify the *literal* inverse-image
open under an original transition. Compactness along that spectral map
and the actual restriction's open embedding give a compact spectral
restricted stage. For a restricted arrow, the compact-open **source**
inclusion is retrocompact and spectral
(`IsRetrocompact_iff_isSpectralMap_subtypeVal`); compose it with the
original spectral transition. `stageMap_fac` identifies this composite
with the restricted map followed by its target inclusion. The official
`SpectralStoneDuality.isSpectralMap_to_subtype_of_comp` then gives
spectrality of the actual arrow. The Type endpoint uses this helper at
`C := Type v` and retains its original public conclusion.

Set `R := restricted N i0 U0` and let `cR` be the forgetful image of
`restrictedCone N i0 m U0`. The inherited `restrictedSpaceIsLimit` supplies
an actual limit for `cR`; the native global-sections theorem then gives
`IsIso (SheafedSpace.nativeGlobalSectionsComparison R cR hcR)` from the
derived spectrality. The imported native-cylinder comparison is opaque.
The proof therefore uses `colimit.hom_ext`, the public coprojection laws
`colimit_ι_restrictedGlobalSectionsComparison` and
`SheafedSpace.colimit_ι_nativeGlobalSectionsComparison`, and
`chosenLimitIso_inv_projection` to identify the *existing* comparison with
native global-sections comparison followed by
`SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op` and
`eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0))`.
All three factors are isomorphisms. The contravariant `Γ` needs `inv.op`.

The example imports the producer ordinarily and keeps
`originalStage_detects_transported_coprojection` **private**. At any actual
original stage `i : Set.Ici i0`, two sections on `stageOpen N i0 U0 i` with
equal images under the original cone projection *after* the
`coneOpen_eq_stage` inverse-image-open cast have equal images in the
restricted-stage colimit *after* the
`SheafedSpace.restrict_Γ_obj` restriction-object cast. It invokes the
proved isomorphism, `originalStage_restrictedGlobalSectionsComparison`,
and injectivity to cancel the actual comparison. The client does not assume
its desired equality, and does not assert broad eventual equality.
