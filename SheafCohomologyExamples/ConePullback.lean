/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.ConePullback
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic


/-! Import-only clients: arbitrary two-arrow diagrams and cones, including an empty vertex. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace SheafCohomologyExamples.ConePullbackClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

/-- The first nonidentity stage map is the mate of the actual native arrow. -/
private theorem type_first_map (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) :
    (SheafedSpace.conePullback (Type v) S c).map first =
      SheafedSpace.triangleMap (Type v)
        (show c.π.app (op (1 : Fin 3)) ≫ (S.map first.op).hom.base =
          c.π.app (op (0 : Fin 3)) from c.w first.op)
        (SheafedSpace.sheafMate (Type v) (S.map first.op)) :=
  SheafedSpace.conePullback_map (Type v) S c first

/-- The second additive stage map uses its native sheaf-side morphism. -/
private theorem additive_second_map (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S c).map second =
      SheafedSpace.triangleMap AddCommGrpCat.{v}
        (show c.π.app (op (2 : Fin 3)) ≫ (S.map second.op).hom.base =
          c.π.app (op (1 : Fin 3)) from c.w second.op)
        (SheafedSpace.sheafMate AddCommGrpCat.{v} (S.map second.op)) :=
  SheafedSpace.conePullback_map AddCommGrpCat.{v} S c second

/-- Two potentially nonidentity stage maps act coherently for arbitrary Type-valued data. -/
private theorem type_chain (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) :
    (SheafedSpace.conePullback (Type v) S c).map first ≫
      (SheafedSpace.conePullback (Type v) S c).map second =
    (SheafedSpace.conePullback (Type v) S c).map (first ≫ second) :=
  ((SheafedSpace.conePullback (Type v) S c).map_comp first second).symm

/-- The same arbitrary two-arrow diagram works for additive sheaves. -/
private theorem additive_chain (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S c).map first ≫
      (SheafedSpace.conePullback AddCommGrpCat.{v} S c).map second =
    (SheafedSpace.conePullback AddCommGrpCat.{v} S c).map (first ≫ second) :=
  ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map_comp first second).symm

/-- Every diagram of underlying spaces has a cone with empty vertex, not assumed limiting. -/
private def emptyCone {J : Type} [Category J] {A : Type u} [Category.{0} A]
    (S : Jᵒᵖ ⥤ SheafedSpace.{u, 0, 0} A) :
    Cone (S ⋙ SheafedSpace.forget A) where
  pt := TopCat.of PEmpty
  π := {
    app := fun _ ↦ TopCat.isInitialPEmpty.to _
    naturality := by
      intro i j f
      exact TopCat.isInitialPEmpty.hom_ext _ _ }

private theorem empty_vertex (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type 0)) :
    (SheafedSpace.conePullback (Type 0) S (emptyCone S)).obj (0 : Fin 3) =
      (TopCat.Sheaf.pullback (Type 0) ((emptyCone S).π.app (op (0 : Fin 3)))).obj
        (S.obj (op (0 : Fin 3))).sheaf :=
  SheafedSpace.conePullback_obj (Type 0) S (emptyCone S) (0 : Fin 3)

/-- Identities still act as identities when the cone vertex is empty. -/
private theorem empty_identity (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) :
    (SheafedSpace.conePullback AddCommGrpCat.{0} S (emptyCone S)).map (𝟙 (0 : Fin 3)) =
      𝟙 ((SheafedSpace.conePullback AddCommGrpCat.{0} S (emptyCone S)).obj (0 : Fin 3)) :=
  (SheafedSpace.conePullback AddCommGrpCat.{0} S (emptyCone S)).map_id (0 : Fin 3)

end SheafCohomologyExamples.ConePullbackClient
