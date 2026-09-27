/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConeOfPullbackCocone
public import Mathlib.CategoryTheory.Adjunction.Limits

public section

/-!
# Limits of sheafed spaces from pullback-sheaf colimits

An actual cone is limiting if its underlying-space cone is limiting and the
cocone of inverse-image sheaves of its native projections is colimiting.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {J : Type wj} [Category.{vj} J]

theorem triangleMap_baseChange {W X Y Z : TopCat.{w}}
    (r : W ⟶ X) {p : X ⟶ Z} {q : X ⟶ Y} {g : Y ⟶ Z}
    {F : Z.Sheaf A} {G : Y.Sheaf A} (hp : q ≫ g = p)
    (a : (TopCat.Sheaf.pullback A g).obj F ⟶ G) :
    (TopCat.Sheaf.pullback A r).map (triangleMap A hp a) ≫
        TopCat.Sheaf.pullbackCompHom A r q G =
      TopCat.Sheaf.pullbackCompHom A r p F ≫
        triangleMap A (show (r ≫ q) ≫ g = r ≫ p by rw [Category.assoc, hp]) a := by
  subst p
  simp [triangleMap]
  conv_lhs =>
    rw [TopCat.Sheaf.pullbackCompHom_naturality]
  have hbase :
      (TopCat.Sheaf.pullback A r).map (TopCat.Sheaf.pullbackCompInv A q g F) ≫
        TopCat.Sheaf.pullbackCompHom A r q ((TopCat.Sheaf.pullback A g).obj F) =
      TopCat.Sheaf.pullbackCompHom A r (q ≫ g) F ≫
        TopCat.Sheaf.pullbackCompInv A (r ≫ q) g F := by
    have hassoc := pullbackCompInv_assoc A r q g F
    have h := congrArg (fun morphism ↦
      TopCat.Sheaf.pullbackCompHom A r (q ≫ g) F ≫ morphism ≫
        TopCat.Sheaf.pullbackCompHom A r q ((TopCat.Sheaf.pullback A g).obj F)) hassoc
    simpa [TopCat.Sheaf.pullbackCompHom, TopCat.Sheaf.pullbackCompInv,
      Category.assoc] using h
  rw [← Category.assoc, hbase, Category.assoc]

/-- Inverse-image sheaves of an extended cone are the pullback of the original
inverse-image diagram, with the canonical composition comparisons. -/
@[expose] noncomputable def conePullbackExtendIso (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) {X : TopCat.{w}} (f : X ⟶ c.pt) :
    conePullback A S c ⋙ TopCat.Sheaf.pullback A f ≅
      conePullback A S (c.extend f) := by
  refine NatIso.ofComponents
    (fun i ↦ (TopCat.Sheaf.pullbackCompIso A f (c.π.app (op i))).app
      (S.obj (op i)).sheaf) ?_
  intro i j a
  exact triangleMap_baseChange A f (c.w a.op) (sheafMate A (S.map a.op))

/-- The comparison of pulled diagrams from equality of projection transformations. -/
@[expose] noncomputable def conePullbackBaseChangeIsoOfPi (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c q : Cone (S ⋙ forget A)) (f : q.pt ⟶ c.pt)
    (hπ : (c.extend f).π = q.π) :
    conePullback A S c ⋙ TopCat.Sheaf.pullback A f ≅ conePullback A S q := by
  have heq : conePullback A S (c.extend f) = conePullback A S q := by
    change conePullback A S (⟨q.pt, (c.extend f).π⟩ : Cone (S ⋙ forget A)) =
      conePullback A S (⟨q.pt, q.π⟩ : Cone (S ⋙ forget A))
    rw [hπ]
  exact conePullbackExtendIso A S c f ≪≫ eqToIso heq

/-- An actual base-cone morphism identifies the pulled sheaf diagrams. -/
@[expose] noncomputable def conePullbackBaseChangeIso (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c q : Cone (S ⋙ forget A)) (f : q.pt ⟶ c.pt)
    (hf : ∀ i, f ≫ c.π.app i = q.π.app i) :
    conePullback A S c ⋙ TopCat.Sheaf.pullback A f ≅ conePullback A S q :=
  conePullbackBaseChangeIsoOfPi A S c q f (by
    apply NatTrans.ext
    funext i
    exact hf i)

private theorem conePullbackBaseChangeIsoOfPi_triangle (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c q : Cone (S ⋙ forget A)) (f : q.pt ⟶ c.pt)
    (hπ : (c.extend f).π = q.π)
    (i : J) {T : c.pt.Sheaf A} (m : (conePullback A S c).obj i ⟶ T) :
    (conePullbackBaseChangeIsoOfPi A S c q f hπ).hom.app i ≫
        triangleMap A (congrArg (fun π : (Functor.const Jᵒᵖ).obj q.pt ⟶
          S ⋙ forget A ↦ π.app (op i)) hπ) m =
      (TopCat.Sheaf.pullback A f).map m := by
  cases q with
  | mk qpt qπ =>
    change qpt ⟶ c.pt at f
    change (c.extend f).π = qπ at hπ
    subst qπ
    simp [conePullbackBaseChangeIsoOfPi, conePullbackExtendIso, triangleMap]

/-- Component cancellation of the base-change comparison against a transported
native sheaf map. -/
theorem conePullbackBaseChangeIso_triangle (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c q : Cone (S ⋙ forget A)) (f : q.pt ⟶ c.pt)
    (hf : ∀ i, f ≫ c.π.app i = q.π.app i)
    (i : J) {T : c.pt.Sheaf A} (m : (conePullback A S c).obj i ⟶ T) :
    (conePullbackBaseChangeIso A S c q f hf).hom.app i ≫
        triangleMap A (hf (op i)) m =
      (TopCat.Sheaf.pullback A f).map m := by
  exact conePullbackBaseChangeIsoOfPi_triangle A S c q f
    (by apply NatTrans.ext; funext j; exact hf j) i m

/-- The colimit extension into a competing native cone's sheaf, after
pulling back the canonical cocone along the unique base-cone map. -/
@[expose] noncomputable def conePullbackLimitTargetCocone (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C)) (Q : Cone S) :
    Cocone (conePullback A S ((forget A).mapCone C) ⋙
      TopCat.Sheaf.pullback A (hbase.lift ((forget A).mapCone Q))) :=
  (Cocone.precompose (conePullbackBaseChangeIso A S
    ((forget A).mapCone C) ((forget A).mapCone Q)
      (hbase.lift ((forget A).mapCone Q))
      (fun i ↦ hbase.fac ((forget A).mapCone Q) i)).hom).obj
    (conePullbackCocone A S Q)

/-- The colimit extension into a competing native cone's sheaf. -/
@[expose] noncomputable def conePullbackLimitSheafMap (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C))
    (Q : Cone S) :
    (TopCat.Sheaf.pullback A (hbase.lift ((forget A).mapCone Q))).obj C.pt.sheaf ⟶
      Q.pt.sheaf :=
  (isColimitOfPreserves
    (TopCat.Sheaf.pullback A (hbase.lift ((forget A).mapCone Q))) hsheaf).desc
    (conePullbackLimitTargetCocone A S C hbase Q)

theorem conePullbackLimitSheafMap_fac (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C))
    (Q : Cone S) (i : J) :
    triangleMap A (hbase.fac ((forget A).mapCone Q) (op i))
        (sheafMate A (C.π.app (op i))) ≫
      conePullbackLimitSheafMap A S C hbase hsheaf Q =
        sheafMate A (Q.π.app (op i)) := by
  let f := hbase.lift ((forget A).mapCone Q)
  let comparison := conePullbackBaseChangeIso A S
    ((forget A).mapCone C) ((forget A).mapCone Q) f
      (fun j ↦ hbase.fac ((forget A).mapCone Q) j)
  apply (cancel_epi (comparison.hom.app i)).mp
  have hfac := (isColimitOfPreserves (TopCat.Sheaf.pullback A f) hsheaf).fac
    (conePullbackLimitTargetCocone A S C hbase Q) i
  simp only [Functor.mapCocone_ι_app, conePullbackCocone_ι_app,
    conePullbackLimitTargetCocone, Cocone.precompose_obj_ι, NatTrans.comp_app] at hfac
  have h1 : comparison.hom.app i ≫
      triangleMap A (hbase.fac ((forget A).mapCone Q) (op i))
        (sheafMate A (C.π.app (op i))) =
      (TopCat.Sheaf.pullback A f).map (sheafMate A (C.π.app (op i))) :=
    conePullbackBaseChangeIso_triangle A S _ _ f _ i _
  have h2 : (TopCat.Sheaf.pullback A f).map (sheafMate A (C.π.app (op i))) ≫
        conePullbackLimitSheafMap A S C hbase hsheaf Q =
      comparison.hom.app i ≫ sheafMate A (Q.π.app (op i)) := hfac
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
    conePullbackLimitSheafMap A S C hbase hsheaf Q) h1).trans h2)

/-- The actual cone's base and projection-mate sheaf cocone determine its
universal lift from an arbitrary competing native cone. -/
@[expose] noncomputable def conePullbackLimitLift (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C))
    (Q : Cone S) : Q.pt ⟶ C.pt := by
  let f : (Q.pt : TopCat) ⟶ (C.pt : TopCat) := hbase.lift ((forget A).mapCone Q)
  exact InducedCategory.homMk {
    base := f
    c := ((TopCat.Sheaf.pullbackPushforwardAdjunction A f).homEquiv _ _
      (conePullbackLimitSheafMap A S C hbase hsheaf Q)).hom }

@[simp] theorem conePullbackLimitLift_base (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C)) (Q : Cone S) :
    (conePullbackLimitLift A S C hbase hsheaf Q).hom.base =
      hbase.lift ((forget A).mapCone Q) := rfl

theorem conePullbackLimitLift_mate (S : Jᵒᵖ ⥤ SheafedSpace A)
    (C : Cone S) (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C)) (Q : Cone S) :
    sheafMate A (conePullbackLimitLift A S C hbase hsheaf Q) =
      conePullbackLimitSheafMap A S C hbase hsheaf Q := by
  unfold sheafMate conePullbackLimitLift
  exact Equiv.symm_apply_apply _ _

/-- A native arrow is determined by its actual base and its inverse-image mate. -/
theorem sheafMate_ext {X Y : SheafedSpace A} (f g : X ⟶ Y)
    (hbase : f.hom.base = g.hom.base)
    (hmate : hbase ▸ sheafMate A f = sheafMate A g) : f = g := by
  rcases f with ⟨⟨fbase, fc⟩⟩
  rcases g with ⟨⟨gbase, gc⟩⟩
  dsimp at hbase
  subst gbase
  apply InducedCategory.hom_ext
  change (⟨fbase, fc⟩ : PresheafedSpace.Hom _ _) = ⟨fbase, gc⟩
  apply PresheafedSpace.hext
    (⟨fbase, fc⟩ : PresheafedSpace.Hom X.toPresheafedSpace Y.toPresheafedSpace)
    (⟨fbase, gc⟩ : PresheafedSpace.Hom X.toPresheafedSpace Y.toPresheafedSpace) rfl
  have hadj := congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A fbase).homEquiv _ _) hmate
  exact Eq.heq (congrArg (fun t ↦ t.hom)
    ((sheafMate_adjoint A (⟨⟨fbase, fc⟩⟩ : X ⟶ Y)).symm.trans
      (hadj.trans (sheafMate_adjoint A (⟨⟨fbase, gc⟩⟩ : X ⟶ Y)))))

/-- A cone of sheafed spaces is limiting when its actual cone of spaces is
limiting and its actual inverse-image sheaf cocone is colimiting. -/
@[expose] noncomputable def isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
    (S : Jᵒᵖ ⥤ SheafedSpace A) (C : Cone S)
    (hbase : IsLimit ((forget A).mapCone C))
    (hsheaf : IsColimit (conePullbackCocone A S C)) : IsLimit C := by
  refine ⟨conePullbackLimitLift A S C hbase hsheaf, ?_, ?_⟩
  · intro Q i
    apply sheafMate_triangle_converse A (Q.π.app i)
      (conePullbackLimitLift A S C hbase hsheaf Q) (C.π.app i)
      (hbase.fac ((forget A).mapCone Q) i)
    rw [conePullbackLimitLift_mate]
    exact conePullbackLimitSheafMap_fac A S C hbase hsheaf Q (unop i)
  · intro Q m hm
    have hmbase : m.hom.base = hbase.lift ((forget A).mapCone Q) := by
      apply hbase.uniq ((forget A).mapCone Q) m.hom.base
      intro i
      exact congrArg (fun arrow : Q.pt ⟶ S.obj i ↦ arrow.hom.base) (hm i)
    rcases m with ⟨⟨mbase, mc⟩⟩
    change mbase = hbase.lift ((forget A).mapCone Q) at hmbase
    subst mbase
    let f := hbase.lift ((forget A).mapCone Q)
    let comparison := conePullbackBaseChangeIso A S
      ((forget A).mapCone C) ((forget A).mapCone Q) f
        (fun i ↦ hbase.fac ((forget A).mapCone Q) i)
    have hmateEq : sheafMate A (⟨⟨f, mc⟩⟩ : Q.pt ⟶ C.pt) =
        conePullbackLimitSheafMap A S C hbase hsheaf Q := by
      apply (isColimitOfPreserves (TopCat.Sheaf.pullback A f) hsheaf).hom_ext
      intro i
      have htri : triangleMap A (hbase.fac ((forget A).mapCone Q) (op i))
          (sheafMate A (C.π.app (op i))) ≫
          sheafMate A (⟨⟨f, mc⟩⟩ : Q.pt ⟶ C.pt) =
            sheafMate A (Q.π.app (op i)) :=
        sheafMate_triangle A (Q.π.app (op i))
          (⟨⟨f, mc⟩⟩ : Q.pt ⟶ C.pt) (C.π.app (op i)) (hm (op i))
      have hboth := htri.trans
        (conePullbackLimitSheafMap_fac A S C hbase hsheaf Q i).symm
      have hpre := congrArg (fun arrow ↦ comparison.hom.app i ≫ arrow) hboth
      have htriangle := conePullbackBaseChangeIso_triangle A S
        ((forget A).mapCone C) ((forget A).mapCone Q) f
          (fun j ↦ hbase.fac ((forget A).mapCone Q) j) i
          (sheafMate A (C.π.app (op i)))
      have hprefix := (Category.assoc _ _ _).trans
        (hpre.trans (Category.assoc _ _ _).symm)
      rw [htriangle] at hprefix
      simp only [Functor.mapCocone_ι_app, conePullbackCocone_ι_app]
      exact hprefix
    refine sheafMate_ext A (⟨⟨f, mc⟩⟩ : Q.pt ⟶ C.pt)
      (conePullbackLimitLift A S C hbase hsheaf Q)
      (by rw [conePullbackLimitLift_base]) ?_
    rw [conePullbackLimitLift_mate]
    simpa only [conePullbackLimitLift_base] using hmateEq

/-- The native cone reconstructed from a limiting space cone and a colimiting
pullback-sheaf cocone is limiting, with its actual projections. -/
noncomputable def coneOfPullbackCoconeIsLimit (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c))
    (hc : IsLimit c) (hK : IsColimit K) :
    IsLimit (coneOfPullbackCocone A S c K) := by
  apply isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone A S
  · rw [coneOfPullbackCocone_forget]
    exact hc
  · have hrecover := conePullbackCocone_coneOfPullbackCocone A S c K
    have htransport : IsColimit ((coneOfPullbackCocone_forget A S c K) ▸
        conePullbackCocone A S (coneOfPullbackCocone A S c K)) := by
      rw [hrecover]
      exact hK
    cases coneOfPullbackCocone_forget A S c K
    exact htransport

end AlgebraicGeometry.SheafedSpace
