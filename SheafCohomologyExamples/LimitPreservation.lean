/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.LimitPreservation
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

/-! Import-only ordinary-preservation API clients for nontrivial and empty shapes. -/

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.LimitPreservation

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

private noncomputable def typeFinite_preservesArbitraryCone
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (native : Cone S) (hnative : IsLimit native) :
    IsLimit ((SheafedSpace.forget (Type v)).mapCone native) := by
  letI : PreservesLimit S (SheafedSpace.forget (Type v)) :=
    SheafedSpace.preservesLimitForgetOfSpaceCone (Type v) S c hc
  exact isLimitOfPreserves _ hnative

private noncomputable def additiveFinite_preservesArbitraryCone
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c)
    (native : Cone S) (hnative : IsLimit native) :
    IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone native) := by
  letI : PreservesLimit S (SheafedSpace.forget AddCommGrpCat.{v}) :=
    SheafedSpace.preservesLimitForgetOfSpaceCone AddCommGrpCat.{v} S c hc
  exact isLimitOfPreserves _ hnative

private theorem typeFinite_chosenProjection
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} (Type v)) :
    letI : HasLimit S := SheafedSpace.hasLimitOfHasLimitForget (Type v) S
    letI : PreservesLimit S (SheafedSpace.forget (Type v)) :=
      SheafedSpace.preservesLimitForgetOfHasLimit (Type v) S
    (preservesLimitIso (SheafedSpace.forget (Type v)) S).hom ≫
        limit.π (S ⋙ SheafedSpace.forget (Type v)) (op (1 : Fin 3)) =
      (SheafedSpace.forget (Type v)).map (limit.π S (op (1 : Fin 3))) := by
  letI : HasLimit S := SheafedSpace.hasLimitOfHasLimitForget (Type v) S
  letI : PreservesLimit S (SheafedSpace.forget (Type v)) :=
    SheafedSpace.preservesLimitForgetOfHasLimit (Type v) S
  exact preservesLimitIso_hom_π (SheafedSpace.forget (Type v)) S (op (1 : Fin 3))

private theorem additiveFinite_chosenWitness
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v}) :
    PreservesLimit S (SheafedSpace.forget AddCommGrpCat.{v}) :=
  SheafedSpace.preservesLimitForgetOfHasLimit AddCommGrpCat.{v} S

private theorem typeFinite_firstArrow
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} (Type v))
    (native : Cone S) :
    ((SheafedSpace.forget (Type v)).mapCone native).π.app (op (1 : Fin 3)) ≫
        (S ⋙ SheafedSpace.forget (Type v)).map first.op =
      ((SheafedSpace.forget (Type v)).mapCone native).π.app (op (0 : Fin 3)) :=
  ((SheafedSpace.forget (Type v)).mapCone native).w first.op

private theorem additiveFinite_secondArrow
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v})
    (native : Cone S) :
    ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone native).π.app (op (2 : Fin 3)) ≫
        (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}).map second.op =
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone native).π.app (op (1 : Fin 3)) :=
  ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone native).w second.op

private def emptyDiagram : PEmpty.{1}ᵒᵖ ⥤ SheafedSpace.{1,0,0} (Type 0) where
  obj := fun i ↦ nomatch i
  map := fun {i} ↦ nomatch i

private noncomputable def empty_preservesArbitraryCone
    (native : Cone emptyDiagram) (hnative : IsLimit native) :
    IsLimit ((SheafedSpace.forget (Type 0)).mapCone native) := by
  letI : PreservesLimit emptyDiagram (SheafedSpace.forget (Type 0)) :=
    SheafedSpace.preservesLimitForgetOfHasLimit (Type 0) emptyDiagram
  exact isLimitOfPreserves _ hnative

private theorem empty_chosenPreservation :
    PreservesLimit emptyDiagram (SheafedSpace.forget (Type 0)) :=
  SheafedSpace.preservesLimitForgetOfHasLimit (Type 0) emptyDiagram

end SheafCohomologyExamples.LimitPreservation
