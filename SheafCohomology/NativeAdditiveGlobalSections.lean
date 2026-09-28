/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Formal Frontier worker-a Hive Task hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004, UID 7b289efe-e184-4c33-9723-7ef39e977b59
-/
module
public import SheafCohomology.NativeLimitGlobalSections
public import SheafCohomology.LimitPreservation
public import SheafCohomology.AbelianForget.LimitPreservation

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Additive global sections of an actual native limit

The global-section maps of the original projections of an additive sheafed-space
cone induce a comparison from the colimit of its additive stage sections.
For filtered spectral diagrams this comparison is an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}) (m : Cone S)

/-- The cocone of additive global sections of the actual native projections. -/
@[expose] noncomputable def nativeAdditiveGlobalSectionsCocone :
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

/-- Comparison of additive stage sections with the actual cone vertex's sections. -/
@[expose] noncomputable def nativeAdditiveGlobalSectionsComparison :
    colimit (S.rightOp ⋙ SheafedSpace.Γ) ⟶ SheafedSpace.Γ.obj (op m.pt) :=
  colimit.desc _ (nativeAdditiveGlobalSectionsCocone S m)

omit [IsFiltered J] in
/-- The additive comparison uses the original native projection at each stage. -/
theorem colimit_ι_nativeAdditiveGlobalSectionsComparison (i : J) :
    colimit.ι (S.rightOp ⋙ SheafedSpace.Γ) i ≫
        nativeAdditiveGlobalSectionsComparison S m =
      SheafedSpace.Γ.map (m.π.app (op i)).op := by
  simpa only [nativeAdditiveGlobalSectionsComparison,
    nativeAdditiveGlobalSectionsCocone] using
    (colimit.ι_desc (nativeAdditiveGlobalSectionsCocone S m) i)

private noncomputable def nativeAdditiveGammaForgetIso
    (X : SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}) :
    (CategoryTheory.forget AddCommGrpCat.{v}).obj (SheafedSpace.Γ.obj (op X)) ≅
      (SheafedSpace.Γ (C := Type v)).obj (op (AbelianForget.underlying.obj X)) :=
  Iso.refl _

/-- Under the identity-on-sections vertex isomorphisms, both morphisms are
the underlying map of the original section component at `op ⊤`. -/
private theorem nativeAdditiveGammaForgetIso_naturality
    {X Y : SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}} (f : X ⟶ Y) :
    (CategoryTheory.forget AddCommGrpCat.{v}).map (SheafedSpace.Γ.map f.op) ≫
        (nativeAdditiveGammaForgetIso X).hom =
      (nativeAdditiveGammaForgetIso Y).hom ≫
        (SheafedSpace.Γ (C := Type v)).map (AbelianForget.underlying.map f).op := by
  change (CategoryTheory.forget AddCommGrpCat.{v}).map (f.hom.c.app (op ⊤)) =
    (CategoryTheory.forget AddCommGrpCat.{v}).map (f.hom.c.app (op ⊤))
  rfl

private noncomputable def nativeAdditiveGammaDiagramForgetIso :
    (S.rightOp ⋙ SheafedSpace.Γ) ⋙ CategoryTheory.forget AddCommGrpCat.{v} ≅
      (S ⋙ AbelianForget.underlying).rightOp ⋙ (SheafedSpace.Γ (C := Type v)) :=
  NatIso.ofComponents
    (fun i => nativeAdditiveGammaForgetIso (S.obj (op i)))
    (by
      intro i j f
      exact nativeAdditiveGammaForgetIso_naturality (S.map f.op))

include m in
/-- Under a chosen native limit, the additive comparison is an isomorphism
for a cofiltered diagram of spectral spaces and spectral transition maps. -/
theorem isIso_nativeAdditiveGlobalSectionsComparison (hm : IsLimit m)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).map f)) :
    IsIso (nativeAdditiveGlobalSectionsComparison S m) := by
  let U : SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v} ⥤ SheafedSpace (Type v) :=
    AbelianForget.underlying
  let F := CategoryTheory.forget AddCommGrpCat.{v}
  let N := S ⋙ U
  let c := (SheafedSpace.forget (Type v)).mapCone (U.mapCone m)
  letI : PreservesLimit S (SheafedSpace.forget AddCommGrpCat.{v}) :=
    SheafedSpace.preservesLimitForgetOfHasLimit AddCommGrpCat.{v} S
  have hspace : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone m) :=
    isLimitOfPreserves (SheafedSpace.forget AddCommGrpCat.{v}) hm
  have hc : IsLimit c := by
    change IsLimit ((SheafedSpace.forget (Type v)).mapCone (U.mapCone m))
    rw [AbelianForget.underlying_mapCone_forget S m]
    exact hspace
  letI : PreservesLimit S U := AbelianForget.preservesCofilteredLimit S
  have hN : IsLimit (U.mapCone m) := isLimitOfPreserves U hm
  let Q := SheafedSpace.limitConeOfSpaceCone (Type v) N c hc
  let e : U.obj m.pt ≅ Q.cone.pt := hN.conePointUniqueUpToIso Q.isLimit
  let A := S.rightOp ⋙ SheafedSpace.Γ
  let D := N.rightOp ⋙ (SheafedSpace.Γ (C := Type v))
  let d : A ⋙ F ≅ D := nativeAdditiveGammaDiagramForgetIso S
  let q : colimit (A ⋙ F) ≅ colimit D := HasColimit.isoOfNatIso d
  let t := nativeAdditiveGammaForgetIso m.pt
  let H : colimit D ⟶ (SheafedSpace.Γ (C := Type v)).obj (op Q.cone.pt) :=
    q.inv ≫ colimit.post A F ≫ F.map (nativeAdditiveGlobalSectionsComparison S m) ≫
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
            F.map (nativeAdditiveGlobalSectionsComparison S m) =
            F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) := by
          rw [← F.map_comp, colimit_ι_nativeAdditiveGlobalSectionsComparison]
        simp only [H, q, HasColimit.ι_isoOfNatIso_inv_assoc,
          colimit.ι_post_assoc]
        have hrew : d.inv.app i ≫
            (F.map (colimit.ι A i) ≫
              F.map (nativeAdditiveGlobalSectionsComparison S m)) ≫
              t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op =
            d.inv.app i ≫ F.map (SheafedSpace.Γ.map (m.π.app (op i)).op) ≫
              t.hom ≫ (SheafedSpace.Γ (C := Type v)).map e.inv.op := by
          rw [hp]
        simpa only [Category.assoc] using hrew
      _ = (SheafedSpace.Γ (C := Type v)).map (U.map (m.π.app (op i))).op ≫
            (SheafedSpace.Γ (C := Type v)).map e.inv.op := by
        have hmap := nativeAdditiveGammaForgetIso_naturality (m.π.app (op i))
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
      (((S ⋙ AbelianForget.underlying) ⋙ SheafedSpace.forget (Type v)).obj k)
    rw [AbelianForget.underlyingDiagram_forget S]
    exact hstage k
  have htransitionN : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f) := by
    intro k l f
    change IsSpectralMap
      (((S ⋙ AbelianForget.underlying) ⋙ SheafedSpace.forget (Type v)).map f)
    rw [AbelianForget.underlyingDiagram_forget S]
    exact htransition f
  have hH : IsIso H := by
    rw [hcomparison]
    exact isIso_nativeGlobalSectionsComparison N c hc hstageN htransitionN
  haveI : IsIso (colimit.post A F) := inferInstance
  haveI : IsIso (F.map (nativeAdditiveGlobalSectionsComparison S m)) := by
    let g := (SheafedSpace.Γ (C := Type v)).map e.inv.op
    haveI : IsIso g := inferInstance
    have h₁ : IsIso ((F.map (nativeAdditiveGlobalSectionsComparison S m) ≫ t.hom) ≫ g) := by
      haveI : IsIso ((q.inv ≫ colimit.post A F) ≫
          ((F.map (nativeAdditiveGlobalSectionsComparison S m) ≫ t.hom) ≫ g)) := by
        simpa only [H, g, Category.assoc] using hH
      exact IsIso.of_isIso_comp_left (q.inv ≫ colimit.post A F) _
    have h₂ : IsIso (F.map (nativeAdditiveGlobalSectionsComparison S m) ≫ t.hom) :=
      IsIso.of_isIso_comp_right _ g
    exact IsIso.of_isIso_comp_right _ t.hom
  exact isIso_of_reflects_iso (nativeAdditiveGlobalSectionsComparison S m) F

end AlgebraicGeometry.SheafedSpace
