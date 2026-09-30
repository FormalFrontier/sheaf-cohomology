/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/







module
import SheafCohomology.NativeOpenRestriction

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-!
# Additive native restriction component readback

Additive adaptation: Formal Frontier Agents, adapting the original
`SheafCohomologyExamples.NativeOpenRestriction` Type client.
The Type client is separately credited to Formal Frontier Agents
through the published history; its proof expression is adapted here,
with upstream mathlib credit explained in `docs/CREDITS.md`.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafedSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeOpenRestrictionAdditive

variable {X Y Z : SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}}

private theorem composed_sections_readback (f : X ⟶ Y) (g : Y ⟶ Z) (W : Opens Z) :
    let U := (Opens.map (f ≫ g).hom.base).obj W
    let V := (Opens.map g.hom.base).obj W
    eqToHom (restrict_Γ_obj Z W).symm ≫
        Γ.map (restrictOnNamedPreimage f V U
            (Opens.map_comp_obj f.hom.base g.hom.base W) ≫
          restrictOnPreimage g W).op ≫
        eqToHom (restrict_Γ_obj X U) =
      (f ≫ g).hom.c.app (op W) ≫
        eqToHom (congrArg (fun T : Opens X => X.presheaf.obj (op T))
          (Opens.map_comp_obj f.hom.base g.hom.base W).symm) := by
  dsimp only
  let U := (Opens.map (f ≫ g).hom.base).obj W
  let V := (Opens.map g.hom.base).obj W
  let h : U = (Opens.map f.hom.base).obj V :=
    Opens.map_comp_obj f.hom.base g.hom.base W
  calc
    eqToHom (restrict_Γ_obj Z W).symm ≫
        Γ.map (restrictOnNamedPreimage f V U h ≫ restrictOnPreimage g W).op ≫
        eqToHom (restrict_Γ_obj X U) =
      (eqToHom (restrict_Γ_obj Z W).symm ≫
          Γ.map (restrictOnPreimage g W).op ≫ eqToHom (restrict_Γ_obj Y V)) ≫
        (eqToHom (restrict_Γ_obj Y V).symm ≫
          Γ.map (restrictOnNamedPreimage f V U h).op ≫
            eqToHom (restrict_Γ_obj X U)) := by
        simp [op_comp, Category.assoc]
    _ = g.hom.c.app (op W) ≫
          (f.hom.c.app (op V) ≫
            eqToHom (congrArg (fun T : Opens X => X.presheaf.obj (op T)) h.symm)) := by
        rw [restrictOnPreimage_Γ_map g W, restrictOnNamedPreimage_Γ_map f V U h]
    _ = (f ≫ g).hom.c.app (op W) ≫
          eqToHom (congrArg (fun T : Opens X => X.presheaf.obj (op T)) h.symm) := by
        rw [comp_hom_c_app']
        dsimp [V]
        rfl

end SheafCohomologyExamples.NativeOpenRestrictionAdditive
