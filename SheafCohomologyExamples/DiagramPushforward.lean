/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.DiagramPushforward
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

/-! Native, public-import-only clients with arbitrary maps and cones. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.DiagramPushforward

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

/-- An actual nonidentity arrow retains its target-space map. -/
private theorem type_first_base (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget (Type v) ⟶ Y) :
    ((SheafedSpace.diagramPushforward (Type v) N Y f).map first.op).hom.base =
      Y.map first.op :=
  SheafedSpace.diagramPushforward_map_base (Type v) N Y f first.op

/-- The other arrow uses the actual additive sheaf map and the strict forward square. -/
private theorem additive_second_sheafMap (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y) :
    (⟨((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map second.op).hom.c⟩ :
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
        (f.app (op (1 : Fin 3)))).obj (N.obj (op (1 : Fin 3))).sheaf ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
        (Y.map second.op)).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{v}
            (f.app (op (2 : Fin 3)))).obj (N.obj (op (2 : Fin 3))).sheaf)) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
        (f.app (op (1 : Fin 3)))).map
          (⟨(N.map second.op).hom.c⟩ :
            (N.obj (op (1 : Fin 3))).sheaf ⟶
            (TopCat.Sheaf.pushforward AddCommGrpCat.{v}
              (N.map second.op).hom.base).obj (N.obj (op (2 : Fin 3))).sheaf) ≫
        (TopCat.Sheaf.SquareTransition.pushforwardSquareIso AddCommGrpCat.{v}
          (N.map second.op).hom.base (Y.map second.op)
          (f.app (op (1 : Fin 3))) (f.app (op (2 : Fin 3)))
          (SheafedSpace.diagramPushforward_square AddCommGrpCat.{v} N Y f second.op)).hom.app
            (N.obj (op (2 : Fin 3))).sheaf :=
  SheafedSpace.diagramPushforward_map_sheafMap AddCommGrpCat.{v} N Y f second.op

/-- The mate of a genuine stage arrow is the square transition, not an assumed identification. -/
private theorem type_first_mate (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget (Type v) ⟶ Y) :
    SheafedSpace.sheafMate (Type v)
        ((SheafedSpace.diagramPushforward (Type v) N Y f).map first.op) =
      TopCat.Sheaf.SquareTransition.transition (Type v)
        (N.map first.op).hom.base (Y.map first.op)
        (f.app (op (0 : Fin 3))) (f.app (op (1 : Fin 3)))
        (SheafedSpace.diagramPushforward_square (Type v) N Y f first.op)
        (SheafedSpace.sheafMate (Type v) (N.map first.op)) :=
  SheafedSpace.diagramPushforward_map_mate (Type v) N Y f first.op

/-- Both nonidentity arrows compose in the native Type-valued diagram. -/
private theorem type_chain (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget (Type v) ⟶ Y) :
    (SheafedSpace.diagramPushforward (Type v) N Y f).map second.op ≫
      (SheafedSpace.diagramPushforward (Type v) N Y f).map first.op =
        (SheafedSpace.diagramPushforward (Type v) N Y f).map (second.op ≫ first.op) :=
  ((SheafedSpace.diagramPushforward (Type v) N Y f).map_comp second.op first.op).symm

/-- The same compositional law applies to additive sheafed-space diagrams. -/
private theorem additive_chain (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y) :
    (SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map second.op ≫
      (SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map first.op =
        (SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map
          (second.op ≫ first.op) :=
  ((SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map_comp
    second.op first.op).symm

/-- A native Type-valued source cone projects by the actual square mate. -/
private theorem type_projection_mate (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget (Type v) ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    SheafedSpace.sheafMate (Type v)
        ((SheafedSpace.diagramPushforwardCone (Type v) N Y f c d g h).π.app
          (op (1 : Fin 3))) =
      TopCat.Sheaf.SquareTransition.transition (Type v)
        (c.π.app (op (1 : Fin 3))).hom.base (d.π.app (op (1 : Fin 3)))
        (f.app (op (1 : Fin 3))) g (h (op (1 : Fin 3)))
        (SheafedSpace.sheafMate (Type v) (c.π.app (op (1 : Fin 3)))) :=
  SheafedSpace.diagramPushforwardCone_projection_mate (Type v) N Y f c d g h
    (op (1 : Fin 3))

/-- The additive cone's native projection law holds on both nonidentity arrows. -/
private theorem additive_cone_chain (N : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (Y : (Fin 3)ᵒᵖ ⥤ TopCat.{v})
    (f : N ⋙ SheafedSpace.forget AddCommGrpCat.{v} ⟶ Y)
    (c : Cone N) (d : Cone Y) (g : (c.pt : TopCat) ⟶ d.pt)
    (h : ∀ i, (c.π.app i).hom.base ≫ f.app i = g ≫ d.π.app i) :
    (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h).π.app
        (op (2 : Fin 3)) ≫
      (SheafedSpace.diagramPushforward AddCommGrpCat.{v} N Y f).map second.op =
        (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h).π.app
          (op (1 : Fin 3)) :=
  (SheafedSpace.diagramPushforwardCone AddCommGrpCat.{v} N Y f c d g h).w second.op

/-- Over the empty index, every native sheafed space forms a genuine source cone. -/
private def emptySourceCone (X : SheafedSpace (Type 0))
    (N : PEmptyᵒᵖ ⥤ SheafedSpace (Type 0)) : Cone N where
  pt := X
  π := { app := fun i ↦ (unop i).elim
         naturality := by intro i; exact (unop i).elim }

/-- The target topological cone is equally native and has arbitrary vertex. -/
private def emptyTargetCone (Z : TopCat.{0})
    (Y : PEmptyᵒᵖ ⥤ TopCat.{0}) : Cone Y where
  pt := Z
  π := { app := fun i ↦ (unop i).elim
         naturality := by intro i; exact (unop i).elim }

/-- The constructor accepts actual native empty-index cones and an arbitrary vertex map. -/
private def emptyNativeCone (X : SheafedSpace (Type 0)) (Z : TopCat.{0})
    (N : PEmptyᵒᵖ ⥤ SheafedSpace (Type 0))
    (Y : PEmptyᵒᵖ ⥤ TopCat.{0})
    (f : N ⋙ SheafedSpace.forget (Type 0) ⟶ Y)
    (g : (X : TopCat) ⟶ Z) :
    Cone (SheafedSpace.diagramPushforward (Type 0) N Y f) :=
  SheafedSpace.diagramPushforwardCone (Type 0) N Y f
    (emptySourceCone X N) (emptyTargetCone Z Y) g
    (fun i ↦ (unop i).elim)

private theorem empty_native_vertex (X : SheafedSpace (Type 0)) (Z : TopCat.{0})
    (N : PEmptyᵒᵖ ⥤ SheafedSpace (Type 0))
    (Y : PEmptyᵒᵖ ⥤ TopCat.{0})
    (f : N ⋙ SheafedSpace.forget (Type 0) ⟶ Y)
    (g : (X : TopCat) ⟶ Z) :
    ((emptyNativeCone X Z N Y f g).pt : TopCat) = Z := rfl

end SheafCohomologyExamples.DiagramPushforward
