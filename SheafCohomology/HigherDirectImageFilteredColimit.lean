/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.HigherDirectImageFilteredColimitPositive

public section

set_option warningAsError true

/-!
# Higher direct images preserve filtered colimits

This file supplies the degree-zero route for additive-commutative-group-valued
sheaves. It first identifies the
presheaf comparison underlying the pushforward of a filtered colimit on every
compact basic open, then proves that the final canonical pushforward and
degree-zero right-derived-pushforward comparisons are isomorphisms and combines
the latter with the positive-degree result for every natural degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
variable [PrespectralSpace X] [QuasiSeparatedSpace X]
variable [PrespectralSpace Y]
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
variable {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})

/-- Pushforward in the selected common universe. -/
abbrev pushforward :
    CategoryTheory.Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⥤
      CategoryTheory.Sheaf
        (Opens.grothendieckTopology Y) AddCommGrpCat.{0} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{0} f

/-- Forgetful functor from sheaves on the target. -/
abbrev forgetY :
    CategoryTheory.Sheaf
        (Opens.grothendieckTopology Y) AddCommGrpCat.{0} ⥤
      Y.Presheaf AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology Y) AddCommGrpCat.{0}

/-- Sections on the inverse image of a target open. -/
abbrev preimageSections (V : Opens Y) :
    CategoryTheory.Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⥤
      AddCommGrpCat.{0} :=
  SheafCohomology.CompactOpenSections.sections ((Opens.map f).obj V)

/-- Sections after pushforward, kept in the definitionally pointwise form. -/
abbrev pushforwardSections (V : Opens Y) :
    CategoryTheory.Sheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⥤
      AddCommGrpCat.{0} :=
  pushforward f ⋙ forgetY (Y := Y) ⋙
    (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op V)

omit [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
theorem pushforwardSections_eq (V : Opens Y) :
    pushforwardSections f V = preimageSections f V := by
  rfl

/-- The pointwise presheaf colimit underlying the explicit colimit of the
pushforward diagram. -/
abbrev underlyingPushforwardPresheafColimit : Y.Presheaf AddCommGrpCat.{0} :=
  colimit (F ⋙ pushforward f ⋙ forgetY (Y := Y))

/-- Before target sheafification, the pushforward comparison is induced by
the source colimit cocone. -/
@[expose] noncomputable def presheafPushforwardColimitComparison :
    underlyingPushforwardPresheafColimit f F ⟶
      (forgetY (Y := Y)).obj ((pushforward f).obj (colimit F)) :=
  colimit.post F (pushforward f ⋙ forgetY (Y := Y))

omit [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
  [IsDirectedOrder I] [Nonempty I] in
/-- On a target open, the presheaf comparison is the canonical comparison for
sections on its inverse image, after the pointwise-colimit isomorphism. -/
theorem presheafPushforwardColimitComparison_app (V : Opens Y) :
    (presheafPushforwardColimitComparison f F).app (op V) =
      (colimitObjIsoColimitCompEvaluation
        (F ⋙ pushforward f ⋙ forgetY (Y := Y)) (op V)).hom ≫
        colimit.post F (pushforwardSections f V) := by
  let D := F ⋙ pushforward f ⋙ forgetY (Y := Y)
  let e := colimitObjIsoColimitCompEvaluation D (op V)
  rw [← cancel_epi e.inv]
  rw [e.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv]
  change
    ((colimit.ι D i).app (op V) ≫
      (colimit.post F (pushforward f ⋙ forgetY (Y := Y))).app (op V)) =
      colimit.ι (F ⋙ pushforwardSections f V) i ≫
        colimit.post F (pushforwardSections f V)
  rw [← NatTrans.comp_app, colimit.ι_post, colimit.ι_post]
  rfl

omit [PrespectralSpace Y]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
/-- On a compact target open, the presheaf comparison is an isomorphism when
the inverse image is compact. -/
theorem presheafPushforwardColimitComparison_app_isIso
    (hf : IsSpectralMap f) (V : Opens Y) (hV : IsCompact (V : Set Y)) :
    IsIso ((presheafPushforwardColimitComparison f F).app (op V)) := by
  rw [presheafPushforwardColimitComparison_app f F V]
  have hpreimage :
      IsCompact ((((Opens.map f).obj V : Opens X) : Set X)) :=
    hf.isCompact_preimage_of_isOpen V.2 hV
  let _ : IsIso (colimit.post F (preimageSections f V)) :=
    SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso
      F ((Opens.map f).obj V) hpreimage
  change IsIso
    ((colimitObjIsoColimitCompEvaluation
      (F ⋙ pushforward f ⋙ forgetY (Y := Y)) (op V)).hom ≫
        colimit.post F (preimageSections f V))
  exact IsIso.comp_isIso'
    (inferInstance : IsIso ((colimitObjIsoColimitCompEvaluation
      (F ⋙ pushforward f ⋙ forgetY (Y := Y)) (op V)).hom))
    (show IsIso (colimit.post F (preimageSections f V)) from ‹_›)

/-- The comparison from the explicit sheafification model of the pushforward
colimit to the pushforward of the source colimit. -/
@[expose] noncomputable def explicitPushforwardColimitComparison :
    (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{0}).obj
        (underlyingPushforwardPresheafColimit f F) ⟶
      (pushforward f).obj (colimit F) :=
  (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{0}).map
      (presheafPushforwardColimitComparison f F) ≫
    (sheafificationAdjunction (Opens.grothendieckTopology Y)
      AddCommGrpCat.{0}).counit.app
      (show CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{0} from (pushforward f).obj (colimit F))

omit [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
/-- The explicit comparison is an isomorphism: on the compact-open basis its
underlying presheaf map is the compact-section comparison on the inverse
image. -/
theorem explicitPushforwardColimitComparison_isIso
    (hf : IsSpectralMap f) :
    IsIso (explicitPushforwardColimitComparison f F) := by
  let J := Opens.grothendieckTopology Y
  let S := presheafToSheaf J AddCommGrpCat.{0}
  let α := presheafPushforwardColimitComparison f F
  let T : CategoryTheory.Sheaf J AddCommGrpCat.{0} :=
    (pushforward f).obj (colimit F)
  let _ : IsIso (S.map α) :=
    HigherDirectImageFilteredColimit.presheafToSheaf_map_isIso_of_isBasis
      (PrespectralSpace.isBasis_opens Y)
      (fun V hV ↦
        presheafPushforwardColimitComparison_app_isIso f F hf V hV)
  let _ : IsIso ((sheafificationAdjunction J AddCommGrpCat.{0}).counit.app T) :=
    inferInstance
  change IsIso
    (S.map α ≫
      (sheafificationAdjunction J AddCommGrpCat.{0}).counit.app T)
  exact IsIso.comp_isIso'
    (show IsIso (S.map α) from ‹_›)
    (show IsIso
      ((sheafificationAdjunction J AddCommGrpCat.{0}).counit.app T) from ‹_›)

omit [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
  [IsDirectedOrder I] [Nonempty I] in
/-- The explicit comparison agrees with the canonical pushforward
`colimit.post` after identifying the explicit source with the chosen sheaf
colimit. -/
theorem explicitPushforwardColimitComparison_eq_canonical :
    (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
        (F ⋙ pushforward f)).hom ≫
        colimit.post F (pushforward f) =
      explicitPushforwardColimitComparison f F := by
  let J := Opens.grothendieckTopology Y
  let T : CategoryTheory.Sheaf J AddCommGrpCat.{0} :=
    (pushforward f).obj (colimit F)
  apply CategoryTheory.Sheaf.hom_ext
  let P := underlyingPushforwardPresheafColimit f F
  let η : sheafify J P ⟶ T.obj :=
    (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
        (F ⋙ pushforward f)).hom.hom ≫
        (colimit.post F (pushforward f)).hom
  let γ : sheafify J P ⟶ T.obj :=
    (explicitPushforwardColimitComparison f F).hom
  change η = γ
  apply sheafify_hom_ext J η γ T.property
  have hrhs :
      toSheafify J P ≫ γ =
        presheafPushforwardColimitComparison f F := by
    dsimp [γ, P, explicitPushforwardColimitComparison]
    rw [← Category.assoc]
    rw [← toSheafify_naturality J
      (presheafPushforwardColimitComparison f F)]
    rw [sheafificationAdjunction_counit_app_val,
      Category.assoc, toSheafify_sheafifyLift]
    exact Category.comp_id _
  rw [hrhs]
  let G : I ⥤ CategoryTheory.Sheaf
      (Opens.grothendieckTopology Y) AddCommGrpCat.{0} :=
    F ⋙ pushforward f
  let p : (colimit G).obj ⟶ T.obj :=
    (colimit.post F (pushforward f)).hom
  change
    toSheafify (Opens.grothendieckTopology Y)
          (SheafCohomology.CompactOpenSections.underlyingPresheafColimit G) ≫
        (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
          G).hom.hom ≫
        p =
      presheafPushforwardColimitComparison f F
  apply colimit.hom_ext
  intro i
  have hunit :
      colimit.ι (G ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) i ≫
          toSheafify (Opens.grothendieckTopology Y)
            (SheafCohomology.CompactOpenSections.underlyingPresheafColimit G) =
        ((SheafCohomology.CompactOpenSections.explicitSheafColimitCocone
          G).ι.app i).hom :=
    (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val
      (colimit.cocone (G ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology Y) AddCommGrpCat.{0})) i).symm
  have hiso := IsColimit.comp_coconePointUniqueUpToIso_hom
    (SheafCohomology.CompactOpenSections.explicitSheafColimitCoconeIsColimit G)
    (colimit.isColimit G) i
  have hisoHom :
      ((SheafCohomology.CompactOpenSections.explicitSheafColimitCocone
          G).ι.app i).hom ≫
          (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
            G).hom.hom =
        (colimit.ι G i).hom :=
    congr_arg (fun k ↦ k.hom) hiso
  calc
    _ = (((SheafCohomology.CompactOpenSections.explicitSheafColimitCocone
          G).ι.app i).hom ≫
          (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
            G).hom.hom) ≫ p := by
            rw [← Category.assoc, hunit]
            rfl
    _ = (colimit.ι G i).hom ≫
          p := by
            exact congr_arg (fun k ↦ k ≫ p) hisoHom
    _ = ((pushforward f).map (colimit.ι F i)).hom := by
      exact congr_arg (fun k ↦ k.hom)
        (colimit.ι_post F (pushforward f) i)
    _ = colimit.ι (G ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) i ≫
          presheafPushforwardColimitComparison f F := by
      exact (colimit.ι_post F
        (pushforward f ⋙ forgetY (Y := Y)) i).symm

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}] in
/-- Under the degree-zero hypotheses, the canonical pushforward
comparison is an isomorphism. -/
theorem pushforward_colimitPost_isIso (hf : IsSpectralMap f) :
    IsIso (colimit.post F (pushforward f)) := by
  let _ : IsIso (explicitPushforwardColimitComparison f F) :=
    explicitPushforwardColimitComparison_isIso f F hf
  apply IsIso.of_isIso_fac_left
    (f := (SheafCohomology.CompactOpenSections.explicitSheafColimitIso
      (F ⋙ pushforward f)).hom)
    (h := explicitPushforwardColimitComparison f F)
  exact explicitPushforwardColimitComparison_eq_canonical f F

section RightDerived

variable [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

omit [HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})] in
/-- The literal degree-zero right-derived-pushforward comparison is an
isomorphism. Preservation is transported through mathlib's canonical
`rightDerivedZeroIsoSelf`, after proving it for pushforward itself. -/
theorem rightDerived_colimitPost_isIso_zero (hf : IsSpectralMap f) :
    IsIso (colimit.post F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived 0)) := by
  let P := pushforward f
  let _ : IsIso (colimit.post F P) :=
    pushforward_colimitPost_isIso f F hf
  let _ : PreservesColimit F P :=
    preservesColimit_of_isIso_post P F
  let _ : P.Additive :=
    TopCat.Sheaf.RightDerivedPushforward.pushforward_additive f
  let _ : P.IsRightAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).isRightAdjoint
  let _ : PreservesColimit F (P.rightDerived 0) :=
    preservesColimit_of_natIso F P.rightDerivedZeroIsoSelf.symm
  change IsIso (colimit.post F (P.rightDerived 0))
  infer_instance

/-- Right-derived pushforward preserves a same-small-universe filtered colimit
in every natural degree. -/
theorem rightDerivedPushforward_preservesColimit
    (hf : IsSpectralMap f) (q : ℕ) :
    PreservesColimit F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) := by
  obtain _ | q := q
  · let _ : IsIso (colimit.post F
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived 0)) :=
      rightDerived_colimitPost_isIso_zero f F hf
    exact preservesColimit_of_isIso_post _ F
  · exact rightDerivedPushforward_preservesColimit_positive
      f F hf (q + 1) (Nat.zero_lt_succ q)

/-- The literal canonical comparison for right-derived pushforward is an
isomorphism in every natural degree. -/
theorem rightDerivedPushforward_colimitPost_isIso
    (hf : IsSpectralMap f) (q : ℕ) :
    IsIso (colimit.post F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q)) := by
  let R := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q
  let hPreserves : PreservesColimit F R := by
    dsimp only [R]
    exact rightDerivedPushforward_preservesColimit f F hf q
  let hF : HasColimit F := by infer_instance
  let e := @preservesColimitIso _ _ _ _ R _ _ F hPreserves hF
  change IsIso e.inv
  infer_instance

omit [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
  [HasExt.{0} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{0})] in
/-- On every stage, the canonical comparison is characterized by the
corresponding right-derived image of the diagram's colimit leg. -/
theorem rightDerivedPushforward_colimitPost_ι (q : ℕ) (i : I) :
    colimit.ι
        (F ⋙ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) i ≫
      colimit.post F
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) =
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q).map
      (colimit.ι F i) :=
  colimit.ι_post F
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) i

end RightDerived

#print axioms presheafPushforwardColimitComparison_app
#print axioms presheafPushforwardColimitComparison_app_isIso
#print axioms explicitPushforwardColimitComparison_isIso
#print axioms explicitPushforwardColimitComparison_eq_canonical
#print axioms pushforward_colimitPost_isIso
#print axioms rightDerived_colimitPost_isIso_zero
#print axioms rightDerivedPushforward_preservesColimit
#print axioms rightDerivedPushforward_colimitPost_isIso
#print axioms rightDerivedPushforward_colimitPost_ι

end SheafCohomology.HigherDirectImageFilteredColimit
