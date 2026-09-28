/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Hive Task hive-request-1c0851150518e166978e650f8b077bcdd9311334
UID: 6ed601e1-657b-408f-bf75-7df21b10a83a
Adapted from the published additive endpoint by Hive Task hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004 (UID 7b289efe-e184-4c33-9723-7ef39e977b59).
Uses the accepted CommRingForget bridge by Hive Task hive-request-c57c813632815e9d350373cdfa7741657fb4852a (UID 2717d143-2755-441e-83fb-8f9190fbe8f1) and the plan by Hive Task hive-request-c122a6d40799b53667ffc3699a7642ef15453985 (UID 911c1933-e837-4a1c-85cd-2dce903e2357).
-/
module
public import SheafCohomology.NativeLimitGlobalSections
public import SheafCohomology.LimitPreservation
public import SheafCohomology.CommRingForget.LimitPreservation
public import Mathlib.Algebra.Category.Ring.FilteredColimits

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Commutative-ring global sections of an actual native limit

The original projections of a native cone induce a cocone of commutative-ring
sections. Its comparison is an isomorphism when the cone limits a cofiltered
diagram of spectral spaces and spectral transition maps. The underlying Type
comparison is identified through the actual cone-point isomorphism, without
replacing the original cone or changing its projections.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J]
    (S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v}) (m : Cone S)

/-- The cocone of ring sections induced by the original native projections. -/
@[expose] noncomputable def nativeCommRingGlobalSectionsCocone :
    Cocone (S.rightOp ⋙ SheafedSpace.Γ) where
  pt := SheafedSpace.Γ.obj (op m.pt)
  ι := {
    app i := SheafedSpace.Γ.map (m.π.app (op i)).op
    naturality := by
      intro i j f
      change SheafedSpace.Γ.map (S.map f.op).op ≫
          SheafedSpace.Γ.map (m.π.app (op j)).op =
        SheafedSpace.Γ.map (m.π.app (op i)).op ≫ 𝟙 _
      rw [Category.comp_id]
      rw [← SheafedSpace.Γ.map_comp]
      congr 1
      rw [← op_comp, m.w f.op]
  }

/-- The canonical comparison from the colimit of stage rings to the sections
of the original native cone vertex. -/
@[expose] noncomputable def nativeCommRingGlobalSectionsComparison :
    colimit (S.rightOp ⋙ SheafedSpace.Γ) ⟶ SheafedSpace.Γ.obj (op m.pt) :=
  colimit.desc _ (nativeCommRingGlobalSectionsCocone S m)

/-- Each comparison leg is the map on sections of the original projection. -/
theorem colimit_ι_nativeCommRingGlobalSectionsComparison (i : J) :
    colimit.ι (S.rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeCommRingGlobalSectionsComparison S m =
      SheafedSpace.Γ.map (m.π.app (op i)).op := by
  simpa only [nativeCommRingGlobalSectionsComparison,
    nativeCommRingGlobalSectionsCocone] using
    (colimit.ι_desc (nativeCommRingGlobalSectionsCocone S m) i)

private noncomputable def nativeCommRingGammaForgetIso
    (X : SheafedSpace.{v + 1, v, v} CommRingCat.{v}) :
    (CategoryTheory.forget CommRingCat.{v}).obj (SheafedSpace.Γ.obj (op X)) ≅
      (SheafedSpace.Γ (C := Type v)).obj (op (CommRingForget.underlying.obj X)) :=
  Iso.refl _

private theorem nativeCommRingGammaForgetIso_naturality
    {X Y : SheafedSpace.{v + 1, v, v} CommRingCat.{v}} (f : X ⟶ Y) :
    (CategoryTheory.forget CommRingCat.{v}).map (SheafedSpace.Γ.map f.op) ≫
        (nativeCommRingGammaForgetIso X).hom =
      (nativeCommRingGammaForgetIso Y).hom ≫
        (SheafedSpace.Γ (C := Type v)).map (CommRingForget.underlying.map f).op := by
  change (CategoryTheory.forget CommRingCat.{v}).map (f.hom.c.app (op ⊤)) =
    (CategoryTheory.forget CommRingCat.{v}).map (f.hom.c.app (op ⊤))
  rfl

private noncomputable def nativeCommRingGammaDiagramForgetIso :
    (S.rightOp ⋙ SheafedSpace.Γ) ⋙ CategoryTheory.forget CommRingCat.{v} ≅
      (S ⋙ CommRingForget.underlying).rightOp ⋙ (SheafedSpace.Γ (C := Type v)) :=
  NatIso.ofComponents
    (fun i => nativeCommRingGammaForgetIso (S.obj (op i)))
    (by
      intro i j f
      exact nativeCommRingGammaForgetIso_naturality (S.map f.op))

variable [IsFiltered J]

/-- For spectral stages and spectral original transition maps, global sections
of any actual native limiting ring cone are the filtered colimit of its stage
section rings. -/
theorem isIso_nativeCommRingGlobalSectionsComparison (hm : IsLimit m)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f)) :
    IsIso (nativeCommRingGlobalSectionsComparison S m) := by
  let U : SheafedSpace.{v + 1, v, v} CommRingCat.{v} ⥤ SheafedSpace (Type v) :=
    CommRingForget.underlying
  let F := CategoryTheory.forget CommRingCat.{v}
  let N := S ⋙ U
  let c := (SheafedSpace.forget (Type v)).mapCone (U.mapCone m)
  letI : PreservesLimit S (SheafedSpace.forget CommRingCat.{v}) :=
    SheafedSpace.preservesLimitForgetOfHasLimit CommRingCat.{v} S
  have hspace : IsLimit ((SheafedSpace.forget CommRingCat.{v}).mapCone m) :=
    isLimitOfPreserves (SheafedSpace.forget CommRingCat.{v}) hm
  have hc : IsLimit c := by
    change IsLimit ((SheafedSpace.forget (Type v)).mapCone (U.mapCone m))
    rw [CommRingForget.underlying_mapCone_forget S m]
    exact hspace
  letI : PreservesLimit S U := CommRingForget.preservesCofilteredLimit S
  have hN : IsLimit (U.mapCone m) := isLimitOfPreserves U hm
  let Q := SheafedSpace.limitConeOfSpaceCone (Type v) N c hc
  let e : U.obj m.pt ≅ Q.cone.pt := hN.conePointUniqueUpToIso Q.isLimit
  let A := S.rightOp ⋙ SheafedSpace.Γ
  let D := N.rightOp ⋙ (SheafedSpace.Γ (C := Type v))
  let d : A ⋙ F ≅ D := nativeCommRingGammaDiagramForgetIso S
  let q : colimit (A ⋙ F) ≅ colimit D := HasColimit.isoOfNatIso d
  let t := nativeCommRingGammaForgetIso m.pt
  let H : colimit D ⟶ (SheafedSpace.Γ (C := Type v)).obj (op Q.cone.pt) :=
    q.inv ≫ colimit.post A F ≫ F.map (nativeCommRingGlobalSectionsComparison S m) ≫
      t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op
  have hcomparison : H = nativeGlobalSectionsComparison N c hc := by
    apply colimit.hom_ext
    intro i
    rw [colimit_ι_nativeGlobalSectionsComparison N c hc i]
    calc
      colimit.ι D i ≫ H =
          d.inv.app i ≫ F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) ≫
            t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op := by
        have hp : F.map (colimit.ι A i) ≫
            F.map (nativeCommRingGlobalSectionsComparison S m) =
            F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) := by
          rw [← F.map_comp, colimit_ι_nativeCommRingGlobalSectionsComparison]
        simp only [H, q, HasColimit.ι_isoOfNatIso_inv_assoc,
          colimit.ι_post_assoc]
        have hrew : d.inv.app i ≫
            (F.map (colimit.ι A i) ≫
              F.map (nativeCommRingGlobalSectionsComparison S m)) ≫
              t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op =
            d.inv.app i ≫ F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) ≫
              t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op := by
          rw [hp]
        simpa only [Category.assoc] using hrew
      _ = (SheafedSpace.Γ (C := Type v)).map (U.map (m.π.app (op i))).op ≫
            (SheafedSpace.Γ (C := Type v)).map e.inv.op := by
        have hmap := nativeCommRingGammaForgetIso_naturality (m.π.app (op i))
        change F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) =
          (SheafedSpace.Γ (C := Type v)).map (U.map (m.π.app (op i))).op at hmap
        exact congrArg (fun f => f ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op)
          hmap
      _ = (SheafedSpace.Γ (C := Type v)).map (Q.cone.π.app (op i)).op := by
        have he : e.inv ≫ U.map (m.π.app (op i)) = Q.cone.π.app (op i) :=
          hN.conePointUniqueUpToIso_inv_comp Q.isLimit (op i)
        rw [← Functor.map_comp, ← op_comp]
        rw [he]
  have hstageN : ∀ k : Jᵒᵖ,
      SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k) := by
    intro k
    change SpectralSpace
      (((S ⋙ CommRingForget.underlying) ⋙ SheafedSpace.forget (Type v)).obj k)
    rw [CommRingForget.underlyingDiagram_forget S]
    exact hstage k
  have htransitionN : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f) := by
    intro k l f
    change IsSpectralMap
      (((S ⋙ CommRingForget.underlying) ⋙ SheafedSpace.forget (Type v)).map f)
    rw [CommRingForget.underlyingDiagram_forget S]
    exact htransition f
  have hH : IsIso H := by
    rw [hcomparison]
    exact isIso_nativeGlobalSectionsComparison N c hc hstageN htransitionN
  haveI : IsIso (colimit.post A F) := inferInstance
  haveI : IsIso (F.map (nativeCommRingGlobalSectionsComparison S m)) := by
    let g := (SheafedSpace.Γ (C := Type v)).map e.inv.op
    haveI : IsIso g := inferInstance
    have h₁ : IsIso ((F.map (nativeCommRingGlobalSectionsComparison S m) ≫ t.hom) ≫ g) := by
      haveI : IsIso ((q.inv ≫ colimit.post A F) ≫
          ((F.map (nativeCommRingGlobalSectionsComparison S m) ≫ t.hom) ≫ g)) := by
        simpa only [H, g, Category.assoc] using hH
      exact IsIso.of_isIso_comp_left (q.inv ≫ colimit.post A F) _
    have h₂ : IsIso (F.map (nativeCommRingGlobalSectionsComparison S m) ≫ t.hom) :=
      IsIso.of_isIso_comp_right _ g
    exact IsIso.of_isIso_comp_right _ t.hom
  exact isIso_of_reflects_iso (nativeCommRingGlobalSectionsComparison S m) F

/-- Each section at the original limit vertex comes from some original stage. -/
theorem exists_nativeCommRingGlobalSections_stage (hm : IsLimit m)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f))
    (r : (SheafedSpace.Γ (C := CommRingCat.{v})).obj (op m.pt)) :
    ∃ (i : J) (a : (SheafedSpace.Γ (C := CommRingCat.{v})).obj (op (S.obj (op i)))),
      SheafedSpace.Γ.map (m.π.app (op i)).op a = r := by
  let A := S.rightOp ⋙ SheafedSpace.Γ
  let F := CategoryTheory.forget CommRingCat.{v}
  let g := nativeCommRingGlobalSectionsComparison S m
  letI : IsIso g := isIso_nativeCommRingGlobalSectionsComparison S m hm hstage htransition
  have hcolimit : IsColimit (F.mapCocone (colimit.cocone A)) :=
    Classical.choice ((inferInstance : PreservesColimit A F).preserves (colimit.isColimit A))
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hcolimit (inv g r)
  refine ⟨i, a, ?_⟩
  change (colimit.ι A i) a = inv g r at ha
  calc
    SheafedSpace.Γ.map (m.π.app (op i)).op a =
        g ((colimit.ι A i) a) := by
      simpa only [CommRingCat.comp_apply] using
        (congrArg (fun f : A.obj i ⟶ (SheafedSpace.Γ (C := CommRingCat.{v})).obj
          (op m.pt) => f a)
          (colimit_ι_nativeCommRingGlobalSectionsComparison S m i)).symm
    _ = g (inv g r) := by rw [ha]
    _ = r := by
      simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
        congrArg (fun f : (SheafedSpace.Γ (C := CommRingCat.{v})).obj (op m.pt) ⟶
          (SheafedSpace.Γ (C := CommRingCat.{v})).obj (op m.pt) => f r)
          (IsIso.inv_hom_id g)


end AlgebraicGeometry.SheafedSpace
