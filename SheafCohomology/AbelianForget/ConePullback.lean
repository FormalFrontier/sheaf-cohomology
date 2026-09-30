/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullback
public import SheafCohomology.AbelianForget.SheafedSpace

public section

/-!
# Pulling back a forgotten additive sheafed-space diagram

For any cone of underlying spaces, the native Type-valued pullback diagram of
the forgotten sheafed spaces agrees canonically with the forgotten additive
pullback diagram. Neither a limit nor a property of the cone's vertex is needed.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v vj wj

namespace TopCat.Sheaf.AbelianForget

variable {W X Y : TopCat.{v}}

/-- The canonical comparison commutes with the inverse native composition maps. -/
theorem canonicalComponent_comp_inv (q : W ⟶ Y) (f : Y ⟶ X)
    (A : X.Sheaf AddCommGrpCat.{v}) :
    TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
      (TopCat.Sheaf.pullback (Type v) q).map (canonicalComponent f A) ≫
        canonicalComponent q ((TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A) =
      canonicalComponent (q ≫ f) A ≫
        (underlyingSheaf W).map (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A) := by
  have compLaw := canonicalComponent_comp q f A
  calc
    _ = TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
          (TopCat.Sheaf.pullback (Type v) q).map (canonicalComponent f A) ≫
            canonicalComponent q ((TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A) ≫
              (underlyingSheaf W).map
                (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} q f A) ≫
                  (underlyingSheaf W).map
                    (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A) := by
      simp only [← Functor.map_comp,
        TopCat.Sheaf.pullbackCompHom, TopCat.Sheaf.pullbackCompInv,
        Iso.hom_inv_id_app]
      simp
    _ = TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
          TopCat.Sheaf.pullbackCompHom (Type v) q f ((underlyingSheaf X).obj A) ≫
            canonicalComponent (q ≫ f) A ≫
              (underlyingSheaf W).map
                (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A) := by
      simpa only [Category.assoc] using congrArg
        (fun arrow ↦ TopCat.Sheaf.pullbackCompInv (Type v) q f
            ((underlyingSheaf X).obj A) ≫ arrow ≫
              (underlyingSheaf W).map
                (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A)) compLaw
    _ = _ := by
      simp [TopCat.Sheaf.pullbackCompHom, TopCat.Sheaf.pullbackCompInv,
        ← Category.assoc]

/-- Forgetting preserves the actual transition across a composable triangle. -/
theorem canonicalComponent_triangleMap (q : W ⟶ Y) (f : Y ⟶ X)
    {A : X.Sheaf AddCommGrpCat.{v}} {B : Y.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A ⟶ B) :
    AlgebraicGeometry.SheafedSpace.triangleMap (Type v)
        (rfl : q ≫ f = q ≫ f)
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫
      canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫
      (underlyingSheaf W).map
        (AlgebraicGeometry.SheafedSpace.triangleMap AddCommGrpCat.{v}
          (rfl : q ≫ f = q ≫ f) a) := by
  change TopCat.Sheaf.pullbackCompInv (Type v) q f ((underlyingSheaf X).obj A) ≫
      (TopCat.Sheaf.pullback (Type v) q).map
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫ canonicalComponent q B =
    canonicalComponent (q ≫ f) A ≫ (underlyingSheaf W).map
      (TopCat.Sheaf.pullbackCompInv AddCommGrpCat.{v} q f A ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{v} q).map a)
  simp only [Functor.map_comp, Category.assoc]
  rw [canonicalComponent_naturality]
  simpa only [Category.assoc] using congrArg
    (fun arrow ↦ arrow ≫ (underlyingSheaf W).map
      ((TopCat.Sheaf.pullback AddCommGrpCat.{v} q).map a))
    (canonicalComponent_comp_inv q f A)

/-- The same law for a separately specified projection and its cone triangle. -/
theorem canonicalComponent_triangleMap_of_comp (p : W ⟶ X) (q : W ⟶ Y)
    (f : Y ⟶ X) (h : q ≫ f = p)
    {A : X.Sheaf AddCommGrpCat.{v}} {B : Y.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A ⟶ B) :
    AlgebraicGeometry.SheafedSpace.triangleMap (Type v) h
        (canonicalComponent f A ≫ (underlyingSheaf Y).map a) ≫
      canonicalComponent q B =
    canonicalComponent p A ≫
      (underlyingSheaf W).map
        (AlgebraicGeometry.SheafedSpace.triangleMap AddCommGrpCat.{v} h a) := by
  subst p
  exact canonicalComponent_triangleMap q f a

end TopCat.Sheaf.AbelianForget

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type wj} [Category.{vj} J]

/-- Strict compatibility of functor association with forgetting the coefficient
structure; no isomorphic replacement of the diagram is needed. -/
theorem underlyingDiagram_forget (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) :
    (S ⋙ underlying) ⋙ SheafedSpace.forget (Type v) =
      S ⋙ SheafedSpace.forget AddCommGrpCat.{v} := by
  rfl

/-- The same cone, with literally the same vertex and projections, over the
underlying Type-valued sheafed-space diagram. -/
@[expose] def underlyingCone (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) :
    Cone ((S ⋙ underlying) ⋙ SheafedSpace.forget (Type v)) where
  pt := c.pt
  π := {
    app := fun i ↦ c.π.app i
    naturality := by
      intro i j a
      change c.π.app j =
        c.π.app i ≫ (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).map a
      exact (c.w a).symm }

@[simp] theorem underlyingCone_pt (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) :
    (underlyingCone S c).pt = c.pt := rfl

@[simp] theorem underlyingCone_π_app (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (i : Jᵒᵖ) :
    (underlyingCone S c).π.app i = c.π.app i := rfl

/-- Both native cone triangles are equal as proofs of the same literal equation. -/
theorem underlyingCone_w (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    {i j : Jᵒᵖ} (a : i ⟶ j) :
    (underlyingCone S c).w a = c.w a := Subsingleton.elim _ _

/-- The native Type mate of the actual forgotten sheafed-space arrow. -/
theorem underlying_sheafMate {X Y : SheafedSpace AddCommGrpCat.{v}} (f : X ⟶ Y) :
    SheafedSpace.sheafMate (Type v) (underlying.map f) =
      canonicalComponent f.hom.base Y.sheaf ≫
        (underlyingSheaf (X : TopCat)).map
          (SheafedSpace.sheafMate AddCommGrpCat.{v} f) :=
  underlying_map_pullback_mate f

/-- The canonical comparison is natural for every actual arrow of a native
cone-pullback diagram. -/
theorem conePullback_naturality (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    {i j : J} (a : i ⟶ j) :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)).map a ≫
      canonicalComponent (c.π.app (op j)) (S.obj (op j)).sheaf =
    canonicalComponent (c.π.app (op i)) (S.obj (op i)).sheaf ≫
      (underlyingSheaf c.pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map a) := by
  have h := canonicalComponent_triangleMap_of_comp
    (c.π.app (op i)) (c.π.app (op j)) (S.map a.op).hom.base (c.w a.op)
    (SheafedSpace.sheafMate AddCommGrpCat.{v} (S.map a.op))
  simp only [Functor.comp_obj, Functor.const_obj_obj, SheafedSpace.forget] at h
  simp only [SheafedSpace.conePullback_obj, SheafedSpace.conePullback_map,
    underlyingCone_π_app, Functor.const_obj_obj,
    Functor.comp_obj, Functor.comp_map, underlying_obj_sheaf,
    underlying_map_base, underlying_sheafMate,
    SheafedSpace.forget] at h ⊢
  rw [underlyingCone_w S c a.op]
  exact h

/-- Canonical natural identification of Type pullbacks with forgotten additive
pullbacks, without assumptions on the diagram or cone. -/
@[expose] def conePullbackIso (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) :
    SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c) ≅
      SheafedSpace.conePullback AddCommGrpCat.{v} S c ⋙ underlyingSheaf c.pt :=
  NatIso.ofComponents
    (fun i ↦ @asIso _ _ _ _
      (canonicalComponent (c.π.app (op i)) (S.obj (op i)).sheaf)
      (canonicalComponent_isIso (c.π.app (op i)) (S.obj (op i)).sheaf))
    (fun {_ _} a ↦ conePullback_naturality S c a)

/-- The forward component is exactly the canonical map at the cone projection. -/
@[simp] theorem conePullbackIso_hom_app
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (i : J) :
    (conePullbackIso S c).hom.app i =
      canonicalComponent (c.π.app (op i)) (S.obj (op i)).sheaf := rfl

/-- The inverse component is the inverse of the canonical projection map. -/
@[simp] theorem conePullbackIso_inv_app
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (i : J) :
    (conePullbackIso S c).inv.app i =
      (canonicalComparisonIso (c.π.app (op i))).inv.app (S.obj (op i)).sheaf := rfl

end AlgebraicGeometry.SheafedSpace.AbelianForget
