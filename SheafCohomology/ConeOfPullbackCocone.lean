/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullbackCocone

public section

/-!
# Reconstructing a native cone from a pullback cocone

An arbitrary cocone of inverse-image sheaves over an actual cone of spaces
supplies the sheaf and native projections of a cone of sheafed spaces.
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

/-- The native vertex has precisely the given carrier and cocone-point sheaf. -/
@[expose] def pullbackCoconeVertex (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) : SheafedSpace A where
  carrier := c.pt
  presheaf := K.pt.1
  IsSheaf := K.pt.2

/-- The native arrow adjoint to one actual inverse-image cocone leg. -/
@[expose] def pullbackCoconeLeg (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) (i : Jᵒᵖ) :
    pullbackCoconeVertex A S c K ⟶ S.obj i :=
  InducedCategory.homMk {
    base := c.π.app i
    c := (((TopCat.Sheaf.pullbackPushforwardAdjunction A (c.π.app i)).homEquiv _ _)
      (K.ι.app (unop i))).hom }

/-- Taking the inverse-image mate recovers the supplied cocone leg exactly. -/
theorem pullbackCoconeLeg_mate (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) (i : Jᵒᵖ) :
    sheafMate A (pullbackCoconeLeg A S c K i) = K.ι.app (unop i) := by
  unfold sheafMate pullbackCoconeLeg
  exact Equiv.symm_apply_apply _ _

/-- A native sheafed-space triangle is recovered from its actual base and mate law. -/
theorem sheafMate_triangle_converse {W X Y : SheafedSpace A}
    (p : W ⟶ X) (q : W ⟶ Y) (f : Y ⟶ X)
    (hbase : q.hom.base ≫ f.hom.base = p.hom.base)
    (hmate : triangleMap A hbase (sheafMate A f) ≫ sheafMate A q =
      sheafMate A p) : q ≫ f = p := by
  rcases p with ⟨⟨pbase, pc⟩⟩
  dsimp at hbase
  subst pbase
  have hmate' : sheafMate A (q ≫ f) =
      sheafMate A (⟨⟨q.hom.base ≫ f.hom.base, pc⟩⟩ : W ⟶ X) := by
    simpa [triangleMap, sheafMate_comp] using hmate
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext (q ≫ f).hom
    (⟨q.hom.base ≫ f.hom.base, pc⟩ : PresheafedSpace.Hom _ _) rfl
  have hAdj := congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction A (q.hom.base ≫ f.hom.base)).homEquiv _ _)
    hmate'
  exact Eq.heq (congrArg (fun t ↦ t.hom)
    ((sheafMate_adjoint A (q ≫ f)).symm.trans
      (hAdj.trans (sheafMate_adjoint A
        (⟨⟨q.hom.base ≫ f.hom.base, pc⟩⟩ : W ⟶ X)))))

/-- Build an actual cone of sheafed spaces from any cocone over the sheaf pullbacks
along an actual cone of underlying spaces. -/
@[expose] def coneOfPullbackCocone (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) : Cone S where
  pt := pullbackCoconeVertex A S c K
  π := {
    app := pullbackCoconeLeg A S c K
    naturality := by
      intro i j f
      change (𝟙 _) ≫ pullbackCoconeLeg A S c K j =
        pullbackCoconeLeg A S c K i ≫ S.map f
      rw [Category.id_comp]
      symm
      apply (sheafMate_triangle_converse A (pullbackCoconeLeg A S c K j)
        (pullbackCoconeLeg A S c K i)
        (S.map f) (c.w f))
      rw [pullbackCoconeLeg_mate, pullbackCoconeLeg_mate]
      change (conePullback A S c).map f.unop ≫ K.ι.app (unop i) =
          K.ι.app (unop j)
      exact K.w f.unop }

@[simp] theorem coneOfPullbackCocone_carrier (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) :
    ((coneOfPullbackCocone A S c K).pt : TopCat) = c.pt := rfl

@[simp] theorem coneOfPullbackCocone_sheaf (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) :
    (coneOfPullbackCocone A S c K).pt.sheaf = K.pt := rfl

@[simp] theorem coneOfPullbackCocone_π_base (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) (i : Jᵒᵖ) :
    ((coneOfPullbackCocone A S c K).π.app i).hom.base = c.π.app i := rfl

@[simp] theorem coneOfPullbackCocone_π_c (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) (i : Jᵒᵖ) :
    ((coneOfPullbackCocone A S c K).π.app i).hom.c =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction A (c.π.app i)).homEquiv _ _)
        (K.ι.app (unop i))).hom := rfl

/-- Each constructed native projection has exactly the original inverse-image mate. -/
theorem coneOfPullbackCocone_π_mate (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) (i : Jᵒᵖ) :
    sheafMate A ((coneOfPullbackCocone A S c K).π.app i) =
      K.ι.app (unop i) :=
  pullbackCoconeLeg_mate A S c K i

/-- Forgetting the native cone yields the original cone of spaces, literally. -/
theorem coneOfPullbackCocone_forget (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) :
    (forget A).mapCone (coneOfPullbackCocone A S c K) = c := by
  cases c with
  | mk pt π =>
    congr 1

/-- The forward mate construction recovers the original cocone after transporting
along equality of the forgotten cone with its supplied base-space cone. -/
theorem conePullbackCocone_coneOfPullbackCocone (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (K : Cocone (conePullback A S c)) :
    (coneOfPullbackCocone_forget A S c K) ▸
      conePullbackCocone A S (coneOfPullbackCocone A S c K) = K := by
  simp only
  cases K with
  | mk pt ι =>
    change Cocone.mk pt
        (conePullbackCocone A S (coneOfPullbackCocone A S c ⟨pt, ι⟩)).ι =
      Cocone.mk pt ι
    congr 1
    apply NatTrans.ext
    funext i
    exact coneOfPullbackCocone_π_mate A S c ⟨pt, ι⟩ (op i)

end AlgebraicGeometry.SheafedSpace
