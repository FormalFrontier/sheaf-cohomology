/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.ConePullbackCocone
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! Import-only clients for arbitrary native `Fin 3` cones and an empty-carrier cone. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.ConePullbackCoconeClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

/-- The first Type-valued leg is the mate of the actual native projection. -/
private theorem type_first (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v)) (c : Cone S) :
    (SheafedSpace.conePullback (Type v) S
        ((SheafedSpace.forget (Type v)).mapCone c)).map first ≫
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (1 : Fin 3) =
      SheafedSpace.sheafMate (Type v) (c.π.app (op (0 : Fin 3))) :=
  SheafedSpace.conePullbackCocone_triangle (Type v) S c first

/-- The second Type-valued arrow has the same native projection-mate law. -/
private theorem type_second (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v)) (c : Cone S) :
    (SheafedSpace.conePullback (Type v) S
        ((SheafedSpace.forget (Type v)).mapCone c)).map second ≫
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (2 : Fin 3) =
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (1 : Fin 3) :=
  (SheafedSpace.conePullbackCocone (Type v) S c).w second

/-- Composition of the two index arrows works for any Type-valued native cone. -/
private theorem type_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v)) (c : Cone S) :
    (SheafedSpace.conePullback (Type v) S
        ((SheafedSpace.forget (Type v)).mapCone c)).map (first ≫ second) ≫
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (2 : Fin 3) =
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (0 : Fin 3) :=
  (SheafedSpace.conePullbackCocone (Type v) S c).w (first ≫ second)

/-- Identities also retain the literal Type-valued projection leg. -/
private theorem type_identity (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v)) (c : Cone S) :
    (SheafedSpace.conePullback (Type v) S
        ((SheafedSpace.forget (Type v)).mapCone c)).map (𝟙 (0 : Fin 3)) ≫
      (SheafedSpace.conePullbackCocone (Type v) S c).ι.app (0 : Fin 3) =
      SheafedSpace.sheafMate (Type v) (c.π.app (op (0 : Fin 3))) :=
  SheafedSpace.conePullbackCocone_triangle (Type v) S c (𝟙 (0 : Fin 3))

/-- Both index arrows remain available for arbitrary additive native cones. -/
private theorem additive_first (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (c : Cone S) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).map first ≫
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (1 : Fin 3) =
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (0 : Fin 3) :=
  (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).w first

private theorem additive_second (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (c : Cone S) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).map second ≫
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (2 : Fin 3) =
      SheafedSpace.sheafMate AddCommGrpCat.{v} (c.π.app (op (1 : Fin 3))) :=
  SheafedSpace.conePullbackCocone_triangle AddCommGrpCat.{v} S c second

private theorem additive_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).map (first ≫ second) ≫
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (2 : Fin 3) =
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (0 : Fin 3) :=
  (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).w (first ≫ second)

private theorem additive_identity (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).map (𝟙 (0 : Fin 3)) ≫
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (0 : Fin 3) =
      (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (0 : Fin 3) :=
  (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).w (𝟙 (0 : Fin 3))

/-- A genuinely empty-carrier sheafed space, constructed from a supplied sheaf. -/
private def emptySheafedSpace (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    SheafedSpace (Type 0) where
  carrier := TopCat.of PEmpty
  presheaf := F.1
  IsSheaf := F.2

/-- A constant native diagram with the supplied empty-carrier object. -/
private def emptyDiagram (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type 0) :=
  (Functor.const _).obj (emptySheafedSpace F)

/-- A native cone, not merely a cone on underlying topological spaces. -/
private def emptyCarrierCone (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    Cone (emptyDiagram F) where
  pt := emptySheafedSpace F
  π := {
    app := fun _ ↦ 𝟙 _
    naturality := by
      intro i j a
      simp [emptyDiagram] }

private theorem empty_carrier (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    ((emptyCarrierCone F).pt : TopCat) = TopCat.of PEmpty := rfl

/-- Even an empty carrier has the literal mate of its *native* projection. -/
private theorem empty_projection_mate (F : (TopCat.of PEmpty).Sheaf (Type 0)) :
    (SheafedSpace.conePullbackCocone (Type 0) (emptyDiagram F)
        (emptyCarrierCone F)).ι.app (0 : Fin 3) =
      SheafedSpace.sheafMate (Type 0) ((emptyCarrierCone F).π.app (op (0 : Fin 3))) :=
  SheafedSpace.conePullbackCocone_ι_app (Type 0) (emptyDiagram F)
    (emptyCarrierCone F) (0 : Fin 3)

/-- Ordinary `colimit.desc` supplies the comparison if a colimit is available. -/
private def colimit_desc (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v)) (c : Cone S)
    [HasColimit (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone c))] :
    colimit (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone c)) ⟶ c.pt.sheaf :=
  colimit.desc _ (SheafedSpace.conePullbackCocone (Type v) S c)

end SheafCohomologyExamples.ConePullbackCoconeClient
