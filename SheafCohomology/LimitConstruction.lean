/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullbackLimit
public import Mathlib.CategoryTheory.Sites.Limits

public section

/-!
# Native limits of sheafed spaces from coefficient colimits

Given a limit cone of underlying spaces, sheafify the colimit of its diagram of
inverse-image sheaves and reconstruct a limiting native cone. The sheaf colimit
instance is local to the construction, rather than a global instance for the
`TopCat.Sheaf` wrapper.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {J : Type wj} [Category.{vj} J] [HasColimitsOfShape J A]

/-- The actual colimit cocone of the inverse-image sheaves over a space cone.
The site-sheaf colimit instance is installed only within this definition. -/
@[expose] noncomputable def conePullbackColimitCocone
    (S : Jᵒᵖ ⥤ SheafedSpace A) (c : Cone (S ⋙ forget A))
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    Cocone (conePullback A S c) := by
  letI : HasColimitsOfShape J (c.pt.Sheaf A) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  exact colimit.cocone _

/-- The chosen cocone is colimiting by the native site-sheaf colimit instance. -/
noncomputable def conePullbackColimitCocone_isColimit
    (S : Jᵒᵖ ⥤ SheafedSpace A) (c : Cone (S ⋙ forget A))
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    IsColimit (conePullbackColimitCocone A S c) := by
  letI : HasColimitsOfShape J (c.pt.Sheaf A) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  exact colimit.isColimit _

/-- Reconstruct a native limiting cone over an actual limiting space cone,
using the actual colimit of the pulled-back sheaf diagram. -/
@[expose] noncomputable def limitConeOfSpaceCone (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] : LimitCone S :=
  ⟨coneOfPullbackCocone A S c (conePullbackColimitCocone A S c),
    coneOfPullbackCoconeIsLimit A S c (conePullbackColimitCocone A S c)
      hc (conePullbackColimitCocone_isColimit A S c)⟩

/-- The native limit's underlying space is literally the selected base. -/
@[simp] theorem limitConeOfSpaceCone_carrier (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    ((limitConeOfSpaceCone A S c hc).cone.pt : TopCat) = c.pt := rfl

/-- The native limit's sheaf is the actual site-sheaf colimit object. -/
@[simp] theorem limitConeOfSpaceCone_sheaf (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    (limitConeOfSpaceCone A S c hc).cone.pt.sheaf =
      (conePullbackColimitCocone A S c).pt := rfl

/-- The colimit-cocone point is definitionally the sheaf colimit object. -/
theorem limitConeOfSpaceCone_sheaf_colimit (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    (limitConeOfSpaceCone A S c hc).cone.pt.sheaf =
      (by letI : HasColimitsOfShape J (c.pt.Sheaf A) :=
            CategoryTheory.Sheaf.instHasColimitsOfShape
          exact (colimit.cocone (conePullback A S c)).pt) := rfl

/-- Forgetting the constructed native cone recovers the whole actual base cone. -/
@[simp] theorem limitConeOfSpaceCone_forget (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] :
    (forget A).mapCone (limitConeOfSpaceCone A S c hc).cone = c :=
  coneOfPullbackCocone_forget A S c (conePullbackColimitCocone A S c)

/-- Each actual projection has exactly the chosen base-cone projection. -/
@[simp] theorem limitConeOfSpaceCone_π_base (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] (i : Jᵒᵖ) :
    ((limitConeOfSpaceCone A S c hc).cone.π.app i).hom.base = c.π.app i := rfl

/-- Each actual native projection has exactly its colimit leg as inverse-image mate. -/
@[simp] theorem limitConeOfSpaceCone_π_mate (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] (i : Jᵒᵖ) :
    sheafMate A ((limitConeOfSpaceCone A S c hc).cone.π.app i) =
      (conePullbackColimitCocone A S c).ι.app (unop i) :=
  pullbackCoconeLeg_mate A S c (conePullbackColimitCocone A S c) i

/-- Each colimit leg, expressed without assuming a wrapper instance globally. -/
theorem limitConeOfSpaceCone_π_mate_colimit_ι (S : Jᵒᵖ ⥤ SheafedSpace A)
    (c : Cone (S ⋙ forget A)) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) A] (i : J) :
    sheafMate A ((limitConeOfSpaceCone A S c hc).cone.π.app (op i)) =
      (by letI : HasColimitsOfShape J (c.pt.Sheaf A) :=
            CategoryTheory.Sheaf.instHasColimitsOfShape
          exact colimit.ι (conePullback A S c) i) :=
  limitConeOfSpaceCone_π_mate A S c hc (op i)

include FA CA

/-- With a chosen space limit, obtain a named limit of the native diagram. -/
theorem hasLimitOfHasLimitForget (S : Jᵒᵖ ⥤ SheafedSpace.{u,w,w} A)
    [HasLimit (S ⋙ forget A)]
    [HasWeakSheafify (Opens.grothendieckTopology
      ((limit (S ⋙ forget A)) : TopCat)) A] :
    HasLimit S := by
  let c : Cone (S ⋙ forget A) := limit.cone (S ⋙ forget A)
  let hc : IsLimit c := limit.isLimit (S ⋙ forget A)
  exact HasLimit.mk (F := S)
    (limitConeOfSpaceCone (FA := FA) (CA := CA) A S c hc)

end AlgebraicGeometry.SheafedSpace
