/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.AbelianForget.ConePullback
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Naturality of cone-wise additive forgetting

The index category has two nonidentity arrows and their composite. The stage
maps and the cone are arbitrary, with no condition on the images of the stage maps.
The empty-vertex example constructs a cone without asserting a limiting property.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SheafedSpace.AbelianForget
open TopCat.Sheaf.AbelianForget

universe v

namespace SheafCohomologyExamples.AbelianForgetConePullbackClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

variable (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
  (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))

private theorem same_vertex : (underlyingCone S c).pt = c.pt := underlyingCone_pt S c

private theorem same_projection (i : Fin 3) :
    (underlyingCone S c).π.app (op i) = c.π.app (op i) :=
  underlyingCone_π_app S c (op i)

private theorem component_first :
    (conePullbackIso S c).hom.app (0 : Fin 3) =
      canonicalComponent (c.π.app (op (0 : Fin 3)))
        (S.obj (op (0 : Fin 3))).sheaf :=
  conePullbackIso_hom_app S c (0 : Fin 3)

private theorem component_second :
    (conePullbackIso S c).hom.app (1 : Fin 3) =
      canonicalComponent (c.π.app (op (1 : Fin 3)))
        (S.obj (op (1 : Fin 3))).sheaf :=
  conePullbackIso_hom_app S c (1 : Fin 3)

private theorem inverse_last :
    (conePullbackIso S c).inv.app (2 : Fin 3) =
      (canonicalComparisonIso (c.π.app (op (2 : Fin 3)))).inv.app
        (S.obj (op (2 : Fin 3))).sheaf :=
  conePullbackIso_inv_app S c (2 : Fin 3)

private theorem first_naturality :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)).map first ≫
      canonicalComponent (c.π.app (op (1 : Fin 3))) (S.obj (op (1 : Fin 3))).sheaf =
    canonicalComponent (c.π.app (op (0 : Fin 3))) (S.obj (op (0 : Fin 3))).sheaf ≫
      (underlyingSheaf c.pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map first) :=
  conePullback_naturality S c first

private theorem second_naturality :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)).map second ≫
      canonicalComponent (c.π.app (op (2 : Fin 3))) (S.obj (op (2 : Fin 3))).sheaf =
    canonicalComponent (c.π.app (op (1 : Fin 3))) (S.obj (op (1 : Fin 3))).sheaf ≫
      (underlyingSheaf c.pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map second) :=
  conePullback_naturality S c second

private theorem composite_naturality :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)).map
        (first ≫ second) ≫
      canonicalComponent (c.π.app (op (2 : Fin 3))) (S.obj (op (2 : Fin 3))).sheaf =
    canonicalComponent (c.π.app (op (0 : Fin 3))) (S.obj (op (0 : Fin 3))).sheaf ≫
      (underlyingSheaf c.pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map (first ≫ second)) := by
  let F : Fin 3 ⥤ TopCat.Sheaf (Type v) c.pt :=
    SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)
  let G : Fin 3 ⥤ TopCat.Sheaf AddCommGrpCat c.pt :=
    SheafedSpace.conePullback AddCommGrpCat S c
  let U : TopCat.Sheaf AddCommGrpCat c.pt ⥤ TopCat.Sheaf (Type v) c.pt :=
    underlyingSheaf c.pt
  let a0 : F.obj 0 ⟶ U.obj (G.obj 0) :=
    canonicalComponent (c.π.app (op (0 : Fin 3))) (S.obj (op (0 : Fin 3))).sheaf
  let a1 : F.obj 1 ⟶ U.obj (G.obj 1) :=
    canonicalComponent (c.π.app (op (1 : Fin 3))) (S.obj (op (1 : Fin 3))).sheaf
  let a2 : F.obj 2 ⟶ U.obj (G.obj 2) :=
    canonicalComponent (c.π.app (op (2 : Fin 3))) (S.obj (op (2 : Fin 3))).sheaf
  have hfirst : F.map first ≫ a1 = a0 ≫ U.map (G.map first) :=
    first_naturality S c
  have hsecond : F.map second ≫ a2 = a1 ≫ U.map (G.map second) :=
    second_naturality S c
  calc
    F.map (first ≫ second) ≫ a2 = (F.map first ≫ F.map second) ≫ a2 :=
      congrArg (fun k => k ≫ a2) (F.map_comp first second)
    _ = F.map first ≫ (F.map second ≫ a2) := Category.assoc _ _ _
    _ = F.map first ≫ (a1 ≫ U.map (G.map second)) :=
      congrArg (fun k => F.map first ≫ k) hsecond
    _ = (F.map first ≫ a1) ≫ U.map (G.map second) := (Category.assoc _ _ _).symm
    _ = (a0 ≫ U.map (G.map first)) ≫ U.map (G.map second) :=
      congrArg (fun k => k ≫ U.map (G.map second)) hfirst
    _ = a0 ≫ (U.map (G.map first) ≫ U.map (G.map second)) := Category.assoc _ _ _
    _ = a0 ≫ U.map (G.map first ≫ G.map second) :=
      congrArg (fun k => a0 ≫ k) (U.map_comp (G.map first) (G.map second)).symm
    _ = a0 ≫ U.map (G.map (first ≫ second)) :=
      congrArg (fun k => a0 ≫ U.map k) (G.map_comp first second).symm

private theorem identity_naturality :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying) (underlyingCone S c)).map
        (𝟙 (0 : Fin 3)) ≫
      canonicalComponent (c.π.app (op (0 : Fin 3))) (S.obj (op (0 : Fin 3))).sheaf =
    canonicalComponent (c.π.app (op (0 : Fin 3))) (S.obj (op (0 : Fin 3))).sheaf ≫
      (underlyingSheaf c.pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{v} S c).map (𝟙 (0 : Fin 3))) :=
  conePullback_naturality S c (𝟙 (0 : Fin 3))

/-- The underlying diagram admits a cone with empty vertex. -/
private def emptyCone (T : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) :
    Cone (T ⋙ SheafedSpace.forget AddCommGrpCat.{0}) where
  pt := TopCat.of PEmpty
  π := {
    app := fun _ ↦ TopCat.isInitialPEmpty.to _
    naturality := by
      intro i j arrow
      exact TopCat.isInitialPEmpty.hom_ext _ _ }

private theorem empty_component
    (T : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) :
    (conePullbackIso T (emptyCone T)).hom.app (0 : Fin 3) =
      canonicalComponent ((emptyCone T).π.app (op (0 : Fin 3)))
        (T.obj (op (0 : Fin 3))).sheaf :=
  conePullbackIso_hom_app T (emptyCone T) (0 : Fin 3)

private theorem empty_composite_naturality
    (T : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) :
    (SheafedSpace.conePullback (Type 0) (T ⋙ underlying)
        (underlyingCone T (emptyCone T))).map (first ≫ second) ≫
      canonicalComponent ((emptyCone T).π.app (op (2 : Fin 3)))
        (T.obj (op (2 : Fin 3))).sheaf =
    canonicalComponent ((emptyCone T).π.app (op (0 : Fin 3)))
        (T.obj (op (0 : Fin 3))).sheaf ≫
      (underlyingSheaf (emptyCone T).pt).map
        ((SheafedSpace.conePullback AddCommGrpCat.{0} T (emptyCone T)).map
          (first ≫ second)) :=
  composite_naturality T (emptyCone T)

end SheafCohomologyExamples.AbelianForgetConePullbackClient
