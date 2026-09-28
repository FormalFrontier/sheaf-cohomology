/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: worker-b Hive Task hive-request-a52411214e83b3e8cc82da1235a39fa07761c413, UID 53f2275c-67d7-4642-adfe-75d218c8d1a9
Planning: worker-a Hive Task hive-request-4fa22ae4ca0e9c3b33a75a991b29940ba8a3b7eb, UID 3903dc2f-29a0-4761-a886-cee3408f2c3e
Dependencies: native cylinder and open naturality by their credited upstream authors
-/
module
public import SheafCohomology.NativeCylinderOpenNaturality

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Change of principal tail for native cylinder sections

The named inverse-image open at a later base stage induces an equivalence of the
actual section diagrams and their colimits, compatibly with every original cone.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
variable {C : Type (v + 1)} [Category.{v} C]

/-- Inclusion of the tail at `j` in the tail at `i0`. -/
@[expose] def betweenTailInclusion (i0 j : ι) (h : i0 ≤ j) :
    Set.Ici j ⥤ Set.Ici i0 :=
  (show Monotone (fun k : Set.Ici j => (⟨k.1, h.trans k.2⟩ : Set.Ici i0)) from
    fun _ _ hk => hk).functor

omit [IsDirectedOrder ι] in
@[simp] theorem betweenTailInclusion_val (i0 j : ι) (h : i0 ≤ j)
    (k : Set.Ici j) : ((betweenTailInclusion i0 j h).obj k).1 = k.1 := rfl

/-- The later principal tail is final in the earlier one. -/
instance betweenTailInclusion_final (i0 j : ι) (h : i0 ≤ j) :
    (betweenTailInclusion i0 j h).Final := by
  letI : IsDirectedOrder (Set.Ici j) := tailDirectedOrder j
  change (show Monotone (fun k : Set.Ici j =>
      (⟨k.1, h.trans k.2⟩ : Set.Ici i0)) from fun _ _ hk => hk).functor.Final
  rw [Monotone.final_functor_iff]
  intro k
  obtain ⟨k', hkk', hjk'⟩ := exists_ge_ge k.1 j
  exact ⟨⟨k', hjk'⟩, hkk'⟩

variable (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C)
  (i0 j : ι) (h : i0 ≤ j) (U : Opens (S.obj (op i0)))

omit [IsDirectedOrder ι] in
/-- The named later-stage open is the corresponding earlier-tail stage open. -/
theorem stageOpen_betweenTail (k : Set.Ici j) :
    stageOpen S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k =
      stageOpen S i0 U ((betweenTailInclusion i0 j h).obj k) := by
  let k0 : Set.Ici i0 := (betweenTailInclusion i0 j h).obj k
  let j0 : Set.Ici i0 := ⟨j, h⟩
  let j1 : Set.Ici j := ⟨j, le_refl j⟩
  let arrow0 : (op k0 : (Set.Ici i0)ᵒᵖ) ⟶ op j0 :=
    (homOfLE k.property).op
  let arrow1 : (op k : (Set.Ici j)ᵒᵖ) ⟶ op j1 :=
    (homOfLE k.property).op
  have hmap : (tailDiagram S i0).map arrow0 =
      (tailDiagram S j).map arrow1 := by
    unfold tailDiagram
    change S.map ((homOfLE k.property).op) = S.map ((homOfLE k.property).op)
    congr 1
  have hleft := (stageOpen_map S i0 U arrow0).symm
  have hright := stageOpen_map S j (stageOpen S i0 U j0) arrow1
  rw [stageOpen_base S j (stageOpen S i0 U j0)] at hright
  change stageOpen S j (stageOpen S i0 U j0) k =
      (Opens.map ((tailDiagram S j).map arrow1).hom.base).obj
        (stageOpen S i0 U j0) at hright
  change (Opens.map ((tailDiagram S i0).map arrow0).hom.base).obj
      (stageOpen S i0 U j0) = stageOpen S i0 U k0 at hleft
  simpa only [hmap, k0, j0] using hright.trans (hmap ▸ hleft)

omit [IsDirectedOrder ι] in
/-- Every cone sees the same named open after moving the principal tail. -/
theorem coneOpen_betweenTail (m : Cone S) :
    coneOpen S j m (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) =
      coneOpen S i0 m U := by
  let j0 : Set.Ici i0 := ⟨j, h⟩
  let j1 : Set.Ici j := ⟨j, le_refl j⟩
  have hleft := coneOpen_eq_stage S i0 m U j0
  have hright := coneOpen_eq_stage S j m (stageOpen S i0 U j0) j1
  rw [stageOpen_base S j (stageOpen S i0 U j0)] at hright
  change coneOpen S j m (stageOpen S i0 U j0) =
    (Opens.map (m.π.app (op j)).hom.base).obj (stageOpen S i0 U j0) at hright
  exact hright.trans hleft.symm

/-- The cast of a native restriction commutes with its inclusion. -/
theorem namedRestrictCast_fac (X : SheafedSpace.{v + 1, v, v} C)
    {V W : Opens X} (e : V = W) :
    eqToHom (congrArg (fun A : Opens X => X.restrict A.isOpenEmbedding) e) ≫
      X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding := by
  cases e
  simp

/-- Literal restricted native sheafed spaces agree after the named stage transport. -/
@[expose] def restrictedBetweenTailIso :
    restricted S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) ≅
      (betweenTailInclusion i0 j h).op ⋙ restricted S i0 U := by
  let V := stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)
  let F := betweenTailInclusion i0 j h
  refine NatIso.ofComponents (fun k => eqToIso
    (congrArg (fun W : Opens (S.obj (op (unop k).1)) =>
      (S.obj (op (unop k).1)).restrict W.isOpenEmbedding)
        (stageOpen_betweenTail S i0 j h U (unop k)))) ?_
  intro a b f
  have hmap : (tailDiagram S j).map f = (tailDiagram S i0).map (F.op.map f) := by
    unfold tailDiagram
    apply congrArg S.map
    exact Subsingleton.elim _ _
  let target := (S.obj (op (unop b).1)).ofRestrict
    (stageOpen S i0 U (F.obj (unop b))).isOpenEmbedding
  haveI : Mono target := inferInstance
  apply (cancel_mono target).1
  simp only [eqToIso.hom, Functor.comp_map, restricted]
  rw [Category.assoc, namedRestrictCast_fac, stageMap_fac]
  dsimp only [target]
  have hfac := stageMap_fac S i0 U (F.op.map f)
  simp only [F, Functor.op_obj, unop_op, betweenTailInclusion_val] at hfac
  rw [Category.assoc, hfac, ← Category.assoc, namedRestrictCast_fac, hmap]
  all_goals first
    | simpa only [Functor.op_obj, unop_op] using
        stageOpen_betweenTail S i0 j h U (unop a)
    | simpa only [Functor.op_obj, unop_op] using
        stageOpen_betweenTail S i0 j h U (unop b)

/-- The actual named-open section diagrams are naturally isomorphic after a tail change. -/
@[expose] def cylinderSectionsTailIso :
    cylinderSections S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) ≅
      betweenTailInclusion i0 j h ⋙ cylinderSections S i0 U := by
  let nativeIso := restrictedBetweenTailIso S i0 j h U
  let oppositeIso :
      (restricted S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))).rightOp ≅
        betweenTailInclusion i0 j h ⋙ (restricted S i0 U).rightOp :=
    { hom := nativeIso.inv.rightOp
      inv := nativeIso.hom.rightOp
      hom_inv_id := by
        rw [← NatTrans.rightOp_comp, nativeIso.hom_inv_id]
        rfl
      inv_hom_id := by
        rw [← NatTrans.rightOp_comp, nativeIso.inv_hom_id]
        rfl }
  exact Functor.isoWhiskerRight oppositeIso SheafedSpace.Γ

omit [IsDirectedOrder ι] in
/-- The section-diagram component is exactly the forward named-open cast. -/
theorem cylinderSectionsTailIso_hom_app (k : Set.Ici j) :
    (cylinderSectionsTailIso S i0 j h U).hom.app k =
      eqToHom (congrArg (fun W : Opens (S.obj (op k.1)) =>
        SheafedSpace.Γ.obj
          (op ((S.obj (op k.1)).restrict W.isOpenEmbedding)))
        (stageOpen_betweenTail S i0 j h U k)) := by
  simp only [cylinderSectionsTailIso, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.rightOp_app,
    restrictedBetweenTailIso, NatIso.ofComponents_inv_app,
    eqToIso.inv, eqToHom_op, eqToHom_map]

omit [IsDirectedOrder ι] in
/-- The section transport commutes with the original-stage Γ identifications. -/
theorem originalStage_cylinderSectionsTailIso (k : Set.Ici j) :
    eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k)).symm ≫
      (cylinderSectionsTailIso S i0 j h U).hom.app k =
    eqToHom (congrArg
        (fun W : Opens (S.obj (op k.1)) => (S.obj (op k.1)).presheaf.obj (op W))
        (stageOpen_betweenTail S i0 j h U k)) ≫
      eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S i0 U ((betweenTailInclusion i0 j h).obj k))).symm := by
  rw [cylinderSectionsTailIso_hom_app]
  simp only [eqToHom_trans]

/-- Original projection components respect simultaneous transports of their
named source and target opens. -/
theorem namedProjection_transport {X Y : SheafedSpace.{v + 1, v, v} C}
    (g : X ⟶ Y) {V W : Opens Y} (e : V = W)
    {A B : Opens X}
    (eV : A = (Opens.map g.hom.base).obj V)
    (eW : B = (Opens.map g.hom.base).obj W)
    (eTarget : A = B) :
    eqToHom (congrArg (fun O : Opens Y => Y.presheaf.obj (op O)) e) ≫
      g.hom.c.app (op W) ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) eW.symm) =
    g.hom.c.app (op V) ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) eV.symm) ≫
      eqToHom (congrArg (fun O : Opens X => X.presheaf.obj (op O)) eTarget) := by
  cases e
  cases eTarget
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A colimit of the earlier section diagram provides the later colimit. -/
theorem hasColimit_cylinderSections_betweenTail
    [HasColimit (cylinderSections S i0 U)] :
    HasColimit (cylinderSections S j
      (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) := by
  letI : HasColimit (betweenTailInclusion i0 j h ⋙ cylinderSections S i0 U) :=
    inferInstance
  exact hasColimit_of_iso (cylinderSectionsTailIso S i0 j h U)

/-- A colimit of the later section diagram also provides the earlier colimit. -/
theorem hasColimit_cylinderSections_of_betweenTail
    [HasColimit (cylinderSections S j
      (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)))] :
    HasColimit (cylinderSections S i0 U) := by
  letI : HasColimit (betweenTailInclusion i0 j h ⋙ cylinderSections S i0 U) :=
    hasColimit_of_iso (cylinderSectionsTailIso S i0 j h U).symm
  exact Functor.Final.hasColimit_of_comp (betweenTailInclusion i0 j h)

attribute [local instance] hasColimit_cylinderSections_betweenTail

/-- The canonical colimit equivalence induced by the actual named-open diagram iso
and finality of the tail inclusion. Only this pair of diagrams needs a colimit. -/
@[expose] def cylinderSectionsTailColimitIso
    [HasColimit (cylinderSections S i0 U)] :
    colimit (cylinderSections S j
      (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) ≅
      colimit (cylinderSections S i0 U) := by
  letI := hasColimit_cylinderSections_betweenTail S i0 j h U
  exact HasColimit.isoOfNatIso (cylinderSectionsTailIso S i0 j h U) ≪≫
    Functor.Final.colimitIso (betweenTailInclusion i0 j h) (cylinderSections S i0 U)

/-- The tail colimit map carries each later coprojection to the corresponding
earlier coprojection after the actual section-object transport. -/
theorem colimit_ι_cylinderSectionsTailColimitIso
    [HasColimit (cylinderSections S i0 U)] (k : Set.Ici j) :
    colimit.ι (cylinderSections S j
      (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) k ≫
      (cylinderSectionsTailColimitIso S i0 j h U).hom =
    (cylinderSectionsTailIso S i0 j h U).hom.app k ≫
      colimit.ι (cylinderSections S i0 U) ((betweenTailInclusion i0 j h).obj k) := by
  letI := hasColimit_cylinderSections_betweenTail S i0 j h U
  simp only [cylinderSectionsTailColimitIso, Iso.trans_hom]
  rw [← Category.assoc,
    HasColimit.ι_isoOfNatIso_hom (cylinderSectionsTailIso S i0 j h U) k,
    Category.assoc,
    Functor.Final.ι_colimitIso_hom (betweenTailInclusion i0 j h)
      (cylinderSections S i0 U) k]

/-- Changing the principal tail commutes with the comparison for every original
cone, with the forward transport between its two named inverse-image opens. -/
theorem cylinderSectionsComparison_betweenTail
    [HasColimit (cylinderSections S i0 U)] (m : Cone S) :
    (cylinderSectionsTailColimitIso S i0 j h U).hom ≫
      cylinderSectionsComparison S i0 m U =
    cylinderSectionsComparison S j m
      (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) ≫
      eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_betweenTail S i0 j h U m)) := by
  let V := stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)
  let F := betweenTailInclusion i0 j h
  letI := hasColimit_cylinderSections_betweenTail S i0 j h U
  apply colimit.hom_ext
  intro k
  let stageSource := eqToHom (SheafedSpace.restrict_Γ_obj
    (S.obj (op k.1)) (stageOpen S j V k)).symm
  haveI : Epi stageSource := inferInstance
  apply (cancel_epi stageSource).1
  calc
    stageSource ≫ colimit.ι (cylinderSections S j V) k ≫
        (cylinderSectionsTailColimitIso S i0 j h U).hom ≫
        cylinderSectionsComparison S i0 m U =
      stageSource ≫ (cylinderSectionsTailIso S i0 j h U).hom.app k ≫
        colimit.ι (cylinderSections S i0 U) (F.obj k) ≫
        cylinderSectionsComparison S i0 m U := by
          simpa only [Category.assoc] using congrArg
            (fun arrow => stageSource ≫ (arrow ≫ cylinderSectionsComparison S i0 m U))
            (colimit_ι_cylinderSectionsTailColimitIso S i0 j h U k)
    _ = (eqToHom (congrArg
          (fun W : Opens (S.obj (op k.1)) =>
            (S.obj (op k.1)).presheaf.obj (op W))
          (stageOpen_betweenTail S i0 j h U k)) ≫
        eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
          (stageOpen S i0 U (F.obj k))).symm) ≫
        colimit.ι (cylinderSections S i0 U) (F.obj k) ≫
        cylinderSectionsComparison S i0 m U := by
          simpa only [Category.assoc] using congrArg
            (fun arrow => arrow ≫
              colimit.ι (cylinderSections S i0 U) (F.obj k) ≫
                cylinderSectionsComparison S i0 m U)
            (originalStage_cylinderSectionsTailIso S i0 j h U k)
    _ = eqToHom (congrArg
          (fun W : Opens (S.obj (op k.1)) =>
            (S.obj (op k.1)).presheaf.obj (op W))
          (stageOpen_betweenTail S i0 j h U k)) ≫
        (m.π.app (op k.1)).hom.c.app (op (stageOpen S i0 U (F.obj k))) ≫
        eqToHom (congrArg
          (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S i0 m U (F.obj k)).symm) := by
          simpa only [F, betweenTailInclusion_val, Category.assoc] using congrArg
            (fun arrow => eqToHom (congrArg
              (fun W : Opens (S.obj (op k.1)) =>
                (S.obj (op k.1)).presheaf.obj (op W))
              (stageOpen_betweenTail S i0 j h U k)) ≫ arrow)
            (originalStage_cylinderSectionsComparison S i0 m U (F.obj k))
    _ = (m.π.app (op k.1)).hom.c.app (op (stageOpen S j V k)) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S j m V k).symm) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_betweenTail S i0 j h U m)) := by
          simpa only [F, betweenTailInclusion_val] using
            namedProjection_transport (m.π.app (op k.1))
              (stageOpen_betweenTail S i0 j h U k)
              (coneOpen_eq_stage S j m V k)
              (coneOpen_eq_stage S i0 m U (F.obj k))
              (coneOpen_betweenTail S i0 j h U m)
    _ = stageSource ≫ colimit.ι (cylinderSections S j V) k ≫
        cylinderSectionsComparison S j m V ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_betweenTail S i0 j h U m)) := by
          simpa only [Category.assoc] using congrArg
            (fun arrow => arrow ≫ eqToHom (congrArg
              (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
              (coneOpen_betweenTail S i0 j h U m)))
            (originalStage_cylinderSectionsComparison S j m V k).symm

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
