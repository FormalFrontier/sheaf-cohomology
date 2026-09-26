/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.Pullback
public import SheafCohomology.SquareTransition

public section

/-!
# Forgetting abelian sheaf square transitions

The canonical pullback/forgetful comparison commutes with the native
unit/counit-defined transition across every commuting square. Both sides use
the strict native sheaf pushforward, with no hypotheses on the spaces or maps.
-/

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.AbelianForget

variable {Xj Xi Yj Yi : TopCat.{v}}

/-- Forgetting an additive sheaf strictly commutes with native pushforward. -/
theorem underlyingSheaf_pushforward_obj (f : Xi ⟶ Yi)
    (F : Xi.Sheaf AddCommGrpCat.{v}) :
    (underlyingSheaf Yi).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj F) =
      (TopCat.Sheaf.pushforward (Type v) f).obj ((underlyingSheaf Xi).obj F) :=
  rfl

/-- Native pushforward of an additive arrow strictly commutes with forgetting. -/
theorem underlyingSheaf_pushforward_map (f : Xi ⟶ Yi)
    {F G : Xi.Sheaf AddCommGrpCat.{v}} (a : F ⟶ G) :
    (underlyingSheaf Yi).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).map a) =
      (TopCat.Sheaf.pushforward (Type v) f).map ((underlyingSheaf Xi).map a) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting carries the forward strict square comparison to the Type-valued
forward strict comparison, including equality transport. -/
theorem underlyingSheaf_pushforwardSquareIso_hom_app
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h : p ≫ fi = fj ≫ q) (G : Xj.Sheaf AddCommGrpCat.{v}) :
    (underlyingSheaf Yi).map
        ((SquareTransition.pushforwardSquareIso AddCommGrpCat.{v} p q fi fj h).hom.app G) =
      (SquareTransition.pushforwardSquareIso (Type v) p q fi fj h).hom.app
        ((underlyingSheaf Xj).obj G) := by
  rw [SquareTransition.pushforwardSquareIso_hom_eq,
    SquareTransition.pushforwardSquareIso_hom_eq]
  erw [eqToHom_app, eqToHom_app]
  change (underlyingSheaf Yi).map
      (eqToHom (congrArg (fun f : Xj ⟶ Yi =>
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj G) h)) =
    eqToHom (congrArg (fun f : Xj ⟶ Yi =>
      (TopCat.Sheaf.pushforward (Type v) f).obj ((underlyingSheaf Xj).obj G)) h)
  rw [eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical forgetful comparison preserves the literal transition
induced by an arbitrary commuting square and additive stage morphism. -/
theorem canonicalComponent_transition (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G) :
    canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
      (underlyingSheaf Yj).map
        (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a) =
      SquareTransition.transition (Type v) p q fi fj h
        (canonicalComponent p F ≫ (underlyingSheaf Xj).map a) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _).injective
  calc
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _)
        (canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
          (underlyingSheaf Yj).map
            (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) =
      (underlyingSheaf Yi).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} q).homEquiv _ _
          (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) :=
      canonicalComponent_mate_map q _ _ _
    _ = (underlyingSheaf Yi).map (SquareTransition.adjoint AddCommGrpCat.{v} q
        (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) := by
      rw [SquareTransition.adjoint_eq_homEquiv]
    _ = (underlyingSheaf Yi).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).map
            (SquareTransition.adjoint AddCommGrpCat.{v} p a) ≫
          (SquareTransition.pushforwardSquareIso AddCommGrpCat.{v}
            p q fi fj h).hom.app G) := by
      rw [SquareTransition.adjoint_transition]
    _ = (TopCat.Sheaf.pushforward (Type v) fi).map
          ((underlyingSheaf Xi).map (SquareTransition.adjoint AddCommGrpCat.{v} p a)) ≫
        (SquareTransition.pushforwardSquareIso (Type v) p q fi fj h).hom.app
          ((underlyingSheaf Xj).obj G) := by
      rw [(underlyingSheaf Yi).map_comp,
        underlyingSheaf_pushforward_map, underlyingSheaf_pushforwardSquareIso_hom_app]
    _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _)
        (SquareTransition.transition (Type v) p q fi fj h
          (canonicalComponent p F ≫ (underlyingSheaf Xj).map a)) := by
      rw [SquareTransition.adjoint_eq_homEquiv AddCommGrpCat.{v} p a]
      rw [← canonicalComponent_mate_map p F G a]
      rw [← SquareTransition.adjoint_eq_homEquiv (Type v) p,
        ← SquareTransition.adjoint_eq_homEquiv (Type v) q]
      exact (SquareTransition.adjoint_transition (Type v) p q fi fj h _).symm

#print axioms underlyingSheaf_pushforward_obj
#print axioms underlyingSheaf_pushforward_map
#print axioms underlyingSheaf_pushforwardSquareIso_hom_app
#print axioms canonicalComponent_transition

end TopCat.Sheaf.AbelianForget
