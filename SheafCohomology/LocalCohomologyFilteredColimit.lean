/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.FilteredColimitFunctorH
public import SheafCohomology.LocalCohomology
public import SheafCohomology.OpenCohomology

public section

set_option warningAsError true

/-!
# Filtered colimits in local cohomology on compact opens

Evaluation of the cohomology
presheaf at a compact basic open is transported through the open over-site to
the corresponding topological subspace, where the filtered-colimit theorem
for sheaf cohomology applies. The final lemmas retain the exact canonical
stage maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X : TopCat.{u}} (U : Opens X)

open CategoryTheory.Sheaf.OpenCohomology

theorem restrictToOver_preservesColimits :
    PreservesColimitsOfSize.{u, u} (restrictToOver U) := by
  let i : TopCat.of U ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let hi : Topology.IsOpenEmbedding i := U.isOpenEmbedding
  let pullbackAdj :=
    TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  let restrictAdj : U.sheafRestrict (C := AddCommGrpCat.{u}) ⊣
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} i :=
    pullbackAdj.ofNatIsoLeft
      (Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u} hi)
  let overEquivAdj :
      (U.sheafEquivOver (A := AddCommGrpCat.{u})).inverse ⊣
        (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor :=
    (U.sheafEquivOver (A := AddCommGrpCat.{u})).symm.toAdjunction
  let compositeAdj := restrictAdj.comp overEquivAdj
  let overPullbackAdj := compositeAdj.ofNatIsoLeft
    U.sheafRestrictSheafEquivOver
  let _ : (restrictToOver U).IsLeftAdjoint := overPullbackAdj.isLeftAdjoint
  infer_instance

#print axioms restrictToOver_preservesColimits

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]
variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]
variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]
variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u})]

/-- The dense-subsite equivalence from the open over-site to the topology on
the open carries the constant integral sheaf to the constant integral sheaf. -/
@[expose] noncomputable def overConstantIso :
    (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.obj
        ((constantSheaf ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u}).obj ↧(ULift ℤ)) ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
        AddCommGrpCat.{u}).obj ↧(ULift ℤ) := by
  let T : Over U := Over.mk (𝟙 U)
  let hT : IsTerminal T := Over.mkIdTerminal
  let hT' : IsTerminal (U.overEquivalence.functor.obj T) :=
    hT.isTerminalObj U.overEquivalence.functor T
  exact (((constantSheafAdj
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} hT).comp
        (U.sheafEquivOver (A := AddCommGrpCat.{u})).toAdjunction).leftAdjointUniq
      (constantSheafAdj (Opens.grothendieckTopology (TopCat.of U))
        AddCommGrpCat.{u} hT')).app ↧(ULift ℤ)

#print axioms overConstantIso

/-- Cohomology on an open over-site agrees additively with cohomology after
transport to the corresponding topological subspace. -/
@[expose] noncomputable def HOverEquivHSubspace
    (G : CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      CategoryTheory.Sheaf.H
        ((U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.obj G) n := by
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  let : E.functor.Additive :=
    E.functor.additive_of_preserves_binary_products
  let : E.inverse.Additive :=
    E.inverse.additive_of_preserves_binary_products
  let A := (constantSheaf ((Opens.grothendieckTopology X).over U)
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let B := (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let e₁ : Abelian.Ext A G n ≃+
      Abelian.Ext A (E.inverse.obj (E.functor.obj G)) n :=
    (((Abelian.extFunctor n).obj (.op A)).mapIso
      (E.unitIso.app G)).addCommGroupIsoToAddEquiv
  let e₂ : Abelian.Ext A (E.inverse.obj (E.functor.obj G)) n ≃+
      Abelian.Ext (E.functor.obj A) (E.functor.obj G) n :=
    E.toAdjunction.extEquiv.symm
  let e₃ : Abelian.Ext (E.functor.obj A) (E.functor.obj G) n ≃+
      Abelian.Ext B (E.functor.obj G) n :=
    (((Abelian.extFunctor n).mapIso (overConstantIso U).symm.op).app
      (E.functor.obj G)).addCommGroupIsoToAddEquiv
  exact e₁.trans (e₂.trans e₃)

#print axioms HOverEquivHSubspace

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over U).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The open-over-site/open-subspace cohomology equivalence is natural in the
coefficient sheaf. -/
theorem HOverEquivHSubspace_naturality
    {G G' : CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}}
    (f : G ⟶ G') (n : ℕ) (x : CategoryTheory.Sheaf.H G n) :
    CategoryTheory.Sheaf.H.map
        ((U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.map f) n
        (HOverEquivHSubspace U G n x) =
      HOverEquivHSubspace U G' n (CategoryTheory.Sheaf.H.map f n x) := by
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  let : E.functor.Additive :=
    E.functor.additive_of_preserves_binary_products
  let : E.inverse.Additive :=
    E.inverse.additive_of_preserves_binary_products
  let A := (constantSheaf ((Opens.grothendieckTopology X).over U)
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let B := (constantSheaf
    (Opens.grothendieckTopology (TopCat.of U))
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let H₁ := (Abelian.extFunctor n).obj (.op A)
  let H₂ := (Abelian.extFunctor n).obj (.op (E.functor.obj A))
  let H₃ := (Abelian.extFunctor n).obj (.op B)
  let e₃ := (Abelian.extFunctor n).mapIso
    (overConstantIso U).symm.op
  have hunit :
      f ≫ E.unitIso.hom.app G' =
        E.unitIso.hom.app G ≫
          E.inverse.map (E.functor.map f) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      E.unitIso.hom.naturality f
  have h₁ :
      H₁.map (E.inverse.map (E.functor.map f))
          (H₁.map (E.unitIso.hom.app G) x) =
        H₁.map (E.unitIso.hom.app G') (H₁.map f x) := by
    calc
      _ = H₁.map (E.unitIso.hom.app G ≫
          E.inverse.map (E.functor.map f)) x := by
        rw [H₁.map_comp, ConcreteCategory.comp_apply]
        rfl
      _ = H₁.map (f ≫ E.unitIso.hom.app G') x := by
        exact congrArg (fun g ↦ H₁.map g x) hunit.symm
      _ = _ := by
        rw [H₁.map_comp, ConcreteCategory.comp_apply]
        rfl
  have h₂ (y : Abelian.Ext A (E.inverse.obj (E.functor.obj G)) n) :
      H₂.map (E.functor.map f) (E.toAdjunction.extEquiv.symm y) =
        E.toAdjunction.extEquiv.symm
          (H₁.map (E.inverse.map (E.functor.map f)) y) := by
    change (E.toAdjunction.extEquiv.symm y).comp
        (Abelian.Ext.mk₀ (E.functor.map f)) (add_zero n) =
      E.toAdjunction.extEquiv.symm
        (y.comp (Abelian.Ext.mk₀
          (E.inverse.map (E.functor.map f))) (add_zero n))
    exact (E.toAdjunction.extEquiv_symm_naturality_right₀
      y (E.functor.map f)).symm
  have h₃ (y : Abelian.Ext (E.functor.obj A) (E.functor.obj G) n) :
      H₃.map (E.functor.map f) (e₃.hom.app (E.functor.obj G) y) =
        e₃.hom.app (E.functor.obj G')
          (H₂.map (E.functor.map f) y) := by
    calc
      _ = (e₃.hom.app (E.functor.obj G) ≫
          H₃.map (E.functor.map f)) y := by
        rw [ConcreteCategory.comp_apply]
      _ = (H₂.map (E.functor.map f) ≫
          e₃.hom.app (E.functor.obj G')) y := by
        rw [e₃.hom.naturality (E.functor.map f)]
      _ = _ := by
        rw [ConcreteCategory.comp_apply]
  change H₃.map (E.functor.map f)
      (e₃.hom.app (E.functor.obj G)
        (E.toAdjunction.extEquiv.symm
          (H₁.map (E.unitIso.hom.app G) x))) =
    e₃.hom.app (E.functor.obj G')
      (E.toAdjunction.extEquiv.symm
        (H₁.map (E.unitIso.hom.app G') (H₁.map f x)))
  rw [h₃, h₂, h₁]

#print axioms HOverEquivHSubspace_naturality

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over U).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- Cohomology on the open over-site and on the corresponding topological
subspace agree as functors of the coefficient sheaf. -/
@[expose] noncomputable def functorHOverIsoFunctorHSubspace (n : ℕ) :
    CategoryTheory.Sheaf.functorH
        ((Opens.grothendieckTopology X).over U) n ≅
      (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor ⋙
        CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology (TopCat.of U)) n :=
  NatIso.ofComponents
    (fun G ↦ (HOverEquivHSubspace U G n).toAddCommGrpIso)
    (fun f ↦ by
      ext x
      exact (HOverEquivHSubspace_naturality U f n x).symm)

#print axioms functorHOverIsoFunctorHSubspace

set_option synthInstance.maxHeartbeats 800000 in
/-- Evaluation of the cohomology presheaf on an open agrees naturally with
cohomology on the corresponding topological subspace.  This is the composite
of the open-over-site comparison and the dense-subsite equivalence. -/
@[expose] noncomputable def cohomologyPresheafEvaluationIsoHSubspace (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n ⋙
        (evaluation _ _).obj (.op U) ≅
      restrictToOver U ⋙
        (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor ⋙
          CategoryTheory.Sheaf.functorH
            (Opens.grothendieckTopology (TopCat.of U)) n :=
  HPrimeIsoHOver U n ≪≫
    Functor.isoWhiskerLeft (restrictToOver U)
      (functorHOverIsoFunctorHSubspace U n)

#print axioms cohomologyPresheafEvaluationIsoHSubspace

section SmallUniversePreservation

variable {X₀ : TopCat.{0}} (U₀ : Opens X₀)
variable [HasSheafify
  (Opens.grothendieckTopology X₀) AddCommGrpCat.{0}]
variable [HasSheafify
  ((Opens.grothendieckTopology X₀).over U₀) AddCommGrpCat.{0}]
variable [HasSheafify
  (Opens.grothendieckTopology (TopCat.of U₀)) AddCommGrpCat.{0}]
variable [(Opens.grothendieckTopology X₀).WEqualsLocallyBijective
  AddCommGrpCat.{0}]
variable [(Opens.grothendieckTopology X₀).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{0})]
variable [((Opens.grothendieckTopology X₀).over U₀).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{0})]
variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X₀) AddCommGrpCat.{0})]
variable [HasExt.{0} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X₀).over U₀) AddCommGrpCat.{0})]
variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of U₀)) AddCommGrpCat.{0})]
variable [PrespectralSpace U₀] [CompactSpace U₀]
  [QuasiSeparatedSpace U₀]
variable {I : Type} [SmallCategory I] [IsFiltered I]
variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X₀) AddCommGrpCat.{0})

/-- On a compact prespectral quasi-separated open, evaluation of the
cohomology presheaf preserves a same-small-universe filtered colimit.  The
proof transports first to the open over-site and then to the corresponding
topological subspace, where the accepted filtered-colimit theorem applies. -/
theorem cohomologyPresheafEvaluation_preservesColimit (n : ℕ) :
    PreservesColimit F
      (CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X₀) n ⋙
        (evaluation _ _).obj (.op U₀)) := by
  let K := restrictToOver U₀
  let E := U₀.sheafEquivOver (A := AddCommGrpCat.{0})
  let HSubspace := CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (TopCat.of U₀)) n
  have hKShape : PreservesColimitsOfShape I (restrictToOver U₀) :=
    (restrictToOver_preservesColimits U₀).preservesColimitsOfShape
  have hK : PreservesColimit F K := hKShape.preservesColimit
  have hE : PreservesColimit (F ⋙ K) E.functor := inferInstance
  have hH : PreservesColimit ((F ⋙ K) ⋙ E.functor) HSubspace :=
    TopCat.Sheaf.preservesColimit_functorH
      (X := TopCat.of U₀) ((F ⋙ K) ⋙ E.functor) n
  have hEH : PreservesColimit (F ⋙ K) (E.functor ⋙ HSubspace) :=
    ⟨fun hc => hH.preserves (hE.preserves hc).some⟩
  have hKEH : PreservesColimit F (K ⋙ E.functor ⋙ HSubspace) :=
    ⟨fun hc => hEH.preserves (hK.preserves hc).some⟩
  exact (preservesColimit_iff_of_natIso F
    (cohomologyPresheafEvaluationIsoHSubspace U₀ n)).mpr hKEH

omit [PrespectralSpace U₀] [CompactSpace U₀]
  [QuasiSeparatedSpace U₀] [IsFiltered I] in
/-- The transported compact-open comparison is the canonical comparison for
cohomology on the topological subspace, with no choice of an unrelated
isomorphism between the same endpoints. -/
theorem cohomologyPresheafEvaluation_colimitPost_transport (n : ℕ)
    [HasColimit F] :
    let e := cohomologyPresheafEvaluationIsoHSubspace U₀ n
    colimMap (Functor.whiskerLeft F e.hom) ≫
        colimit.post F
          (restrictToOver U₀ ⋙
            (U₀.sheafEquivOver (A := AddCommGrpCat.{0})).functor ⋙
              CategoryTheory.Sheaf.functorH
                (Opens.grothendieckTopology (TopCat.of U₀)) n) =
      colimit.post F
          (CategoryTheory.Sheaf.cohomologyPresheafFunctor
              (Opens.grothendieckTopology X₀) n ⋙
            (evaluation _ _).obj (.op U₀)) ≫
        e.hom.app (colimit F) := by
  dsimp only
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, ι_colimMap, Category.assoc, colimit.ι_post,
    colimit.ι_post_assoc]
  exact ((cohomologyPresheafEvaluationIsoHSubspace U₀ n).hom.naturality
    (colimit.ι F i)).symm

omit [PrespectralSpace U₀] [CompactSpace U₀]
  [QuasiSeparatedSpace U₀] [IsFiltered I] in
/-- On every filtered stage, the transported compact-open comparison is
literally the cohomology map induced by that stage's canonical map to the
colimit, after the fixed open-subspace comparison at the source stage. -/
@[reassoc]
theorem cohomologyPresheafEvaluation_colimitPost_transport_stage
    (n : ℕ) (i : I) [HasColimit F] :
    let e := cohomologyPresheafEvaluationIsoHSubspace U₀ n
    colimit.ι
          (F ⋙ CategoryTheory.Sheaf.cohomologyPresheafFunctor
              (Opens.grothendieckTopology X₀) n ⋙
            (evaluation _ _).obj (.op U₀)) i ≫
        colimMap (Functor.whiskerLeft F e.hom) ≫
          colimit.post F
            (restrictToOver U₀ ⋙
              (U₀.sheafEquivOver (A := AddCommGrpCat.{0})).functor ⋙
                CategoryTheory.Sheaf.functorH
                  (Opens.grothendieckTopology (TopCat.of U₀)) n) =
      e.hom.app (F.obj i) ≫
        (restrictToOver U₀ ⋙
          (U₀.sheafEquivOver (A := AddCommGrpCat.{0})).functor ⋙
            CategoryTheory.Sheaf.functorH
              (Opens.grothendieckTopology (TopCat.of U₀)) n).map
                (colimit.ι F i) := by
  dsimp only
  rw [← Category.assoc, ι_colimMap, Category.assoc, colimit.ι_post]
  rfl

#print axioms cohomologyPresheafEvaluation_preservesColimit
#print axioms cohomologyPresheafEvaluation_colimitPost_transport
#print axioms cohomologyPresheafEvaluation_colimitPost_transport_stage

end SmallUniversePreservation

end SheafCohomology.HigherDirectImageFilteredColimit
