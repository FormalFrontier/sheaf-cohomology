/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.SquareTransition

public section

/-!
# Clients of the abelian-forgetful square-transition law

These statements import only the public library API and use native transitions
for arbitrary stages, target composition, identity/empty spaces and pasted
squares.
-/

set_option warningAsError true

universe v

open CategoryTheory

namespace SheafCohomologyExamples.AbelianForgetSquareTransition

open TopCat.Sheaf.AbelianForget TopCat.Sheaf.SquareTransition

variable {Xj Xi Yj Yi : TopCat.{v}}

private theorem arbitrary_stage (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G) :
    canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
      (underlyingSheaf Yj).map (transition AddCommGrpCat.{v} p q fi fj h a) =
    transition (Type v) p q fi fj h
      (canonicalComponent p F ≫ (underlyingSheaf Xj).map a) :=
  canonicalComponent_transition p q fi fj h a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem target_postcomposition (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G H : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G) (b : G ⟶ H) :
    canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
      (underlyingSheaf Yj).map (transition AddCommGrpCat.{v} p q fi fj h (a ≫ b)) =
    transition (Type v) p q fi fj h
        (canonicalComponent p F ≫ (underlyingSheaf Xj).map a) ≫
      (TopCat.Sheaf.pushforward (Type v) fj).map ((underlyingSheaf Xj).map b) := by
  rw [transition_comp AddCommGrpCat.{v} p q fi fj h a b,
    (underlyingSheaf Yj).map_comp, ← Category.assoc,
    canonicalComponent_transition, underlyingSheaf_pushforward_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem identity_square (f : Xi ⟶ Yi) (F : Xi.Sheaf AddCommGrpCat.{v}) :
    canonicalComponent (𝟙 Yi) ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj F) ≫
      (underlyingSheaf Yi).map
        (identity AddCommGrpCat.{v} ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} f).obj F)) =
    identity (Type v) ((TopCat.Sheaf.pushforward (Type v) f).obj ((underlyingSheaf Xi).obj F)) := by
  calc
    _ = transition (Type v) (𝟙 Xi) (𝟙 Yi) f f (by simp)
        (canonicalComponent (𝟙 Xi) F ≫
          (underlyingSheaf Xi).map (identity AddCommGrpCat.{v} F)) := by
      rw [← transition_identity AddCommGrpCat.{v} f F]
      exact canonicalComponent_transition (𝟙 Xi) (𝟙 Yi) f f (by simp)
        (identity AddCommGrpCat.{v} F)
    _ = transition (Type v) (𝟙 Xi) (𝟙 Yi) f f (by simp)
          (identity (Type v) ((underlyingSheaf Xi).obj F)) := by
      have hId : canonicalComponent (𝟙 Xi) F ≫
          (underlyingSheaf Xi).map (identity AddCommGrpCat.{v} F) =
          identity (Type v) ((underlyingSheaf Xi).obj F) := by
        apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (𝟙 Xi)).homEquiv _ _).injective
        rw [canonicalComponent_mate_map]
        rw [← adjoint_eq_homEquiv AddCommGrpCat.{v} (𝟙 Xi),
          ← adjoint_eq_homEquiv (Type v) (𝟙 Xi)]
        rw [adjoint_identity, adjoint_identity, (underlyingSheaf Xi).map_id]
      rw [hId]
    _ = _ := transition_identity (Type v) f ((underlyingSheaf Xi).obj F)

private theorem empty_space_identity
    (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    canonicalComponent (𝟙 (TopCat.of PEmpty))
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 (TopCat.of PEmpty))).obj F) ≫
      (underlyingSheaf (TopCat.of PEmpty)).map
        (identity AddCommGrpCat.{0}
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (𝟙 (TopCat.of PEmpty))).obj F)) =
    identity (Type 0)
      ((TopCat.Sheaf.pushforward (Type 0) (𝟙 (TopCat.of PEmpty))).obj
        ((underlyingSheaf (TopCat.of PEmpty)).obj F)) :=
  identity_square (𝟙 (TopCat.of PEmpty)) F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem pasted_square {Xk Yk : TopCat.{v}}
    (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    (qjk : Yk ⟶ Yj) (qij : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (fk : Xk ⟶ Yk)
    (hij : pij ≫ fi = fj ≫ qij) (hjk : pjk ≫ fj = fk ≫ qjk)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    {H : Xk.Sheaf AddCommGrpCat.{v}}
    (aij : (TopCat.Sheaf.pullback AddCommGrpCat.{v} pij).obj F ⟶ G)
    (ajk : (TopCat.Sheaf.pullback AddCommGrpCat.{v} pjk).obj G ⟶ H) :
    canonicalComponent (qjk ≫ qij)
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
      (underlyingSheaf Yk).map
        (composite AddCommGrpCat.{v} qjk qij
          (transition AddCommGrpCat.{v} pij qij fi fj hij aij)
          (transition AddCommGrpCat.{v} pjk qjk fj fk hjk ajk)) =
    transition (Type v) (pjk ≫ pij) (qjk ≫ qij) fi fk
      (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])
      (canonicalComponent (pjk ≫ pij) F ≫
        (underlyingSheaf Xk).map (composite AddCommGrpCat.{v} pjk pij aij ajk)) := by
  rw [← transition_composite AddCommGrpCat.{v} pjk pij qjk qij fi fj fk hij hjk aij ajk]
  exact canonicalComponent_transition (pjk ≫ pij) (qjk ≫ qij) fi fk
    (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])
    (composite AddCommGrpCat.{v} pjk pij aij ajk)

#print axioms arbitrary_stage
#print axioms target_postcomposition
#print axioms identity_square
#print axioms empty_space_identity
#print axioms pasted_square

end SheafCohomologyExamples.AbelianForgetSquareTransition
