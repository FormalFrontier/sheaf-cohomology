/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.SquareTransition
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

public section

set_option warningAsError true

/-! Import-only clients for the native square transition, with no source-research dependencies. -/

noncomputable section

open CategoryTheory

universe v

namespace SheafCohomologyExamples.SquareTransition

open TopCat.Sheaf.SquareTransition

variable {Xk Xj Xi Yk Yj Yi : TopCat.{v}}

private theorem type_square_mate
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h : p ≫ fi = fj ≫ q) {F : Xi.Sheaf (Type v)} {G : Xj.Sheaf (Type v)}
    (a : (TopCat.Sheaf.pullback (Type v) p).obj F ⟶ G) :
    adjoint (Type v) q (transition (Type v) p q fi fj h a) =
      (TopCat.Sheaf.pushforward (Type v) fi).map (adjoint (Type v) p a) ≫
        (pushforwardSquareIso (Type v) p q fi fj h).hom.app G :=
  adjoint_transition (Type v) p q fi fj h a

private theorem abelian_square_mate
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G) :
    adjoint AddCommGrpCat.{v} q (transition AddCommGrpCat.{v} p q fi fj h a) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).map
          (adjoint AddCommGrpCat.{v} p a) ≫
        (pushforwardSquareIso AddCommGrpCat.{v} p q fi fj h).hom.app G :=
  adjoint_transition AddCommGrpCat.{v} p q fi fj h a

private theorem type_target_naturality
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h : p ≫ fi = fj ≫ q) {F : Xi.Sheaf (Type v)}
    {G H : Xj.Sheaf (Type v)}
    (a : (TopCat.Sheaf.pullback (Type v) p).obj F ⟶ G)
    (b : G ⟶ H) :
    transition (Type v) p q fi fj h (a ≫ b) =
      transition (Type v) p q fi fj h a ≫
        (TopCat.Sheaf.pushforward (Type v) fj).map b :=
  transition_comp (Type v) p q fi fj h a b

private theorem abelian_target_naturality
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h : p ≫ fi = fj ≫ q) {F : Xi.Sheaf AddCommGrpCat.{v}}
    {G H : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G)
    (b : G ⟶ H) :
    transition AddCommGrpCat.{v} p q fi fj h (a ≫ b) =
      transition AddCommGrpCat.{v} p q fi fj h a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} fj).map b :=
  transition_comp AddCommGrpCat.{v} p q fi fj h a b

private theorem type_square_proof_irrel
    (p : Xj ⟶ Xi) (q : Yj ⟶ Yi) (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h h' : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf (Type v)} {G : Xj.Sheaf (Type v)}
    (a : (TopCat.Sheaf.pullback (Type v) p).obj F ⟶ G) :
    transition (Type v) p q fi fj h a = transition (Type v) p q fi fj h' a :=
  transition_proof_irrel (Type v) p q fi fj h h' a

private theorem type_identity (fi : Xi ⟶ Yi) (F : Xi.Sheaf (Type v)) :
    transition (Type v) (𝟙 Xi) (𝟙 Yi) fi fi (by simp) (identity (Type v) F) =
      identity (Type v) ((TopCat.Sheaf.pushforward (Type v) fi).obj F) :=
  transition_identity (Type v) fi F

private theorem abelian_identity (fi : Xi ⟶ Yi) (F : Xi.Sheaf AddCommGrpCat.{v}) :
    transition AddCommGrpCat.{v} (𝟙 Xi) (𝟙 Yi) fi fi (by simp)
      (identity AddCommGrpCat.{v} F) =
      identity AddCommGrpCat.{v}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) :=
  transition_identity AddCommGrpCat.{v} fi F

private theorem empty_type_identity (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    transition (Type 0) (𝟙 (TopCat.of PEmpty)) (𝟙 (TopCat.of PEmpty))
      (𝟙 (TopCat.of PEmpty)) (𝟙 (TopCat.of PEmpty)) (by simp)
      (identity (Type 0) F) =
      identity (Type 0)
        ((TopCat.Sheaf.pushforward (Type 0) (𝟙 (TopCat.of PEmpty))).obj F) :=
  transition_identity (Type 0) (𝟙 (TopCat.of PEmpty)) F

private theorem empty_abelian_identity (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    transition AddCommGrpCat.{0} (𝟙 (TopCat.of PEmpty)) (𝟙 (TopCat.of PEmpty))
      (𝟙 (TopCat.of PEmpty)) (𝟙 (TopCat.of PEmpty)) (by simp)
      (identity AddCommGrpCat.{0} F) =
      identity AddCommGrpCat.{0}
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0}
          (𝟙 (TopCat.of PEmpty))).obj F) :=
  transition_identity AddCommGrpCat.{0} (𝟙 (TopCat.of PEmpty)) F

private theorem type_two_square_pasting
    (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    (qjk : Yk ⟶ Yj) (qij : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (fk : Xk ⟶ Yk)
    (hij : pij ≫ fi = fj ≫ qij) (hjk : pjk ≫ fj = fk ≫ qjk)
    {F : Xi.Sheaf (Type v)} {G : Xj.Sheaf (Type v)}
    {H : Xk.Sheaf (Type v)}
    (aij : (TopCat.Sheaf.pullback (Type v) pij).obj F ⟶ G)
    (ajk : (TopCat.Sheaf.pullback (Type v) pjk).obj G ⟶ H) :
    transition (Type v) (pjk ≫ pij) (qjk ≫ qij) fi fk
      (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])
      (composite (Type v) pjk pij aij ajk) =
    composite (Type v) qjk qij
      (transition (Type v) pij qij fi fj hij aij)
      (transition (Type v) pjk qjk fj fk hjk ajk) :=
  transition_composite (Type v) pjk pij qjk qij fi fj fk hij hjk aij ajk

private theorem abelian_two_square_pasting
    (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    (qjk : Yk ⟶ Yj) (qij : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (fk : Xk ⟶ Yk)
    (hij : pij ≫ fi = fj ≫ qij) (hjk : pjk ≫ fj = fk ≫ qjk)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    {H : Xk.Sheaf AddCommGrpCat.{v}}
    (aij : (TopCat.Sheaf.pullback AddCommGrpCat.{v} pij).obj F ⟶ G)
    (ajk : (TopCat.Sheaf.pullback AddCommGrpCat.{v} pjk).obj G ⟶ H) :
    transition AddCommGrpCat.{v} (pjk ≫ pij) (qjk ≫ qij) fi fk
      (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])
      (composite AddCommGrpCat.{v} pjk pij aij ajk) =
    composite AddCommGrpCat.{v} qjk qij
      (transition AddCommGrpCat.{v} pij qij fi fj hij aij)
      (transition AddCommGrpCat.{v} pjk qjk fj fk hjk ajk) :=
  transition_composite AddCommGrpCat.{v} pjk pij qjk qij fi fj fk hij hjk aij ajk

#print axioms type_square_mate
#print axioms abelian_square_mate
#print axioms type_target_naturality
#print axioms abelian_target_naturality
#print axioms type_square_proof_irrel
#print axioms type_identity
#print axioms abelian_identity
#print axioms empty_type_identity
#print axioms empty_abelian_identity
#print axioms type_two_square_pasting
#print axioms abelian_two_square_pasting

end SheafCohomologyExamples.SquareTransition
