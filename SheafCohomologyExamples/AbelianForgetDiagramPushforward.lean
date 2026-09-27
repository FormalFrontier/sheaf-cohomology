module

public import SheafCohomology.AbelianForget.DiagramPushforward
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

/-!
# Private clients of coefficient-forgetting native diagram pushforward

The two Fin 3 stage arrows and their composite use arbitrary genuine diagram
maps, not identity or invertibility hypotheses. Cones use an arbitrary
continuous vertex map and their actual projection squares. The empty index
also admits a genuine native cone comparison.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SheafedSpace.AbelianForget

universe v

namespace SheafCohomologyExamples.AbelianForgetDiagramPushforwardClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

variable (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
  (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
  (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)

private theorem finite_diagram :
    SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f ⋙ underlying =
      SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f :=
  underlying_diagramPushforward N Y f

private theorem first_arrow :
    underlying.map ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map first.op) =
      (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map first.op :=
  underlying_diagramPushforward_map N Y f first.op

private theorem second_arrow_base :
    (underlying.map
      ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map second.op)).hom.base =
      Y.map second.op :=
  underlying_diagramPushforward_map_base N Y f second.op

/-- The actual two nonidentity arrows and their composite respect the strict
diagram identification. -/
private theorem finite_composite :
    underlying.map
      ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map
        (second.op ≫ first.op)) =
      (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map second.op ≫
        (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map first.op := by
  rw [underlying_diagramPushforward_map]
  exact (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map_comp
    second.op first.op

variable (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
  (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i)

private def finite_cone :
    (Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
        (underlying.mapCone
          (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h)) ≅
      SheafedSpace.diagramPushforwardCone (Type v) (N ⋙ underlying) Y f
        (underlying.mapCone c) d g h :=
  underlying_diagramPushforwardConeIso N Y f c d g h

private theorem finite_projection :
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).π.app
          (op (1 : Fin 3)) =
      (SheafedSpace.diagramPushforwardCone (Type v) (N ⋙ underlying) Y f
        (underlying.mapCone c) d g h).π.app (op (1 : Fin 3)) :=
  underlying_diagramPushforwardCone_projection N Y f c d g h _

/-- The transported projections satisfy the actual cone law across a
nonidentity stage arrow, with no constraint on the vertex map `g`. -/
private theorem finite_projection_chain :
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).π.app
          (op (2 : Fin 3)) ≫
      (SheafedSpace.diagramPushforward (Type v) (N ⋙ underlying) Y f).map second.op =
    ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
      (underlying.mapCone
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).π.app
          (op (1 : Fin 3)) :=
  ((Cone.postcompose (eqToHom (underlying_diagramPushforward N Y f))).obj
    (underlying.mapCone
      (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h))).w second.op

/-- Native empty-index cones do not require an inhabited index category. -/
private def emptySourceCone (X : SheafedSpace AddCommGrpCat.{0})
    (S : PEmptyᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) : Cone S where
  pt := X
  π := { app := fun i ↦ (unop i).elim
         naturality := by intro i; exact (unop i).elim }

private def emptyTargetCone (Z : TopCat.{0})
    (T : PEmptyᵒᵖ ⥤ TopCat.{0}) : Cone T where
  pt := Z
  π := { app := fun i ↦ (unop i).elim
         naturality := by intro i; exact (unop i).elim }

private def empty_index (X : SheafedSpace AddCommGrpCat.{0}) (Z : TopCat.{0})
    (S : PEmptyᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0})
    (T : PEmptyᵒᵖ ⥤ TopCat.{0})
    (u : S ⋙ SheafedSpace.forget AddCommGrpCat.{0} ⟶ T)
    (vertex : (X : TopCat) ⟶ Z) :
    (Cone.postcompose (eqToHom (underlying_diagramPushforward S T u))).obj
        (underlying.mapCone
          (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{0} S T u
            (emptySourceCone X S) (emptyTargetCone Z T) vertex
            (fun i ↦ (unop i).elim))) ≅
      SheafedSpace.diagramPushforwardCone (Type 0) (S ⋙ underlying) T u
        (underlying.mapCone (emptySourceCone X S)) (emptyTargetCone Z T) vertex
        (fun i ↦ (unop i).elim) :=
  underlying_diagramPushforwardConeIso S T u
    (emptySourceCone X S) (emptyTargetCone Z T) vertex (fun i ↦ (unop i).elim)

end SheafCohomologyExamples.AbelianForgetDiagramPushforwardClient
