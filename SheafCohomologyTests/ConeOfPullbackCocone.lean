/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.ConeOfPullbackCocone
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic


/-! Public-import clients for arbitrary inverse-image cocones, including the empty index. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.ConeOfPullbackCoconeClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

/-- The first native projection triangle uses an arbitrary Type-valued diagram. -/
private theorem type_first (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (1 : Fin 3)) ≫
      S.map first.op =
      (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (0 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone (Type v) S c K).w first.op

/-- The second nonidentity index arrow retains its actual stage map. -/
private theorem type_second (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (2 : Fin 3)) ≫
      S.map second.op =
      (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (1 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone (Type v) S c K).w second.op

/-- The native projections respect the composite of the two index arrows. -/
private theorem type_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (2 : Fin 3)) ≫
      S.map (first ≫ second).op =
      (SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (0 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone (Type v) S c K).w (first ≫ second).op

private theorem type_mate (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    SheafedSpace.sheafMate (Type v)
      ((SheafedSpace.coneOfPullbackCocone (Type v) S c K).π.app (op (1 : Fin 3))) =
      K.ι.app (1 : Fin 3) :=
  SheafedSpace.coneOfPullbackCocone_π_mate (Type v) S c K _

private theorem type_forget (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    (SheafedSpace.forget (Type v)).mapCone
      (SheafedSpace.coneOfPullbackCocone (Type v) S c K) = c :=
  SheafedSpace.coneOfPullbackCocone_forget (Type v) S c K

private theorem type_roundtrip (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c)) :
    (SheafedSpace.coneOfPullbackCocone_forget (Type v) S c K) ▸
      SheafedSpace.conePullbackCocone (Type v) S
        (SheafedSpace.coneOfPullbackCocone (Type v) S c K) = K :=
  SheafedSpace.conePullbackCocone_coneOfPullbackCocone (Type v) S c K

/-- The additive client likewise uses arbitrary stage arrows. -/
private theorem additive_first (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c)) :
    (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
      (op (1 : Fin 3)) ≫ S.map first.op =
      (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
        (op (0 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).w first.op

private theorem additive_second (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c)) :
    (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
      (op (2 : Fin 3)) ≫ S.map second.op =
      (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
        (op (1 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).w second.op

private theorem additive_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c)) :
    (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
      (op (2 : Fin 3)) ≫ S.map (first ≫ second).op =
      (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
        (op (0 : Fin 3)) :=
  (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).w (first ≫ second).op

private theorem additive_mate (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c)) :
    SheafedSpace.sheafMate AddCommGrpCat.{v}
      ((SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app
        (op (2 : Fin 3))) = K.ι.app (2 : Fin 3) :=
  SheafedSpace.coneOfPullbackCocone_π_mate AddCommGrpCat.{v} S c K _

private theorem additive_forget (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c)) :
    (SheafedSpace.forget AddCommGrpCat.{v}).mapCone
      (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K) = c :=
  SheafedSpace.coneOfPullbackCocone_forget AddCommGrpCat.{v} S c K

/-- An empty index allows an entirely arbitrary sheaf as cocone vertex. -/
private def emptyCocone (S : PEmptyᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (F : c.pt.Sheaf (Type v)) :
    Cocone (SheafedSpace.conePullback (Type v) S c) where
  pt := F
  ι := {
    app := fun i ↦ nomatch i
    naturality := by
      intro i
      exact nomatch i }

private theorem empty_vertex (S : PEmptyᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (F : c.pt.Sheaf (Type v)) :
    (SheafedSpace.coneOfPullbackCocone (Type v) S c (emptyCocone S c F)).pt.sheaf =
      F := rfl

private theorem empty_forget (S : PEmptyᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (F : c.pt.Sheaf (Type v)) :
    (SheafedSpace.forget (Type v)).mapCone
      (SheafedSpace.coneOfPullbackCocone (Type v) S c (emptyCocone S c F)) = c :=
  SheafedSpace.coneOfPullbackCocone_forget (Type v) S c _

end SheafCohomologyExamples.ConeOfPullbackCoconeClient
