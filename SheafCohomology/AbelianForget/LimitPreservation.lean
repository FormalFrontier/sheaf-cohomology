/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.FilteredColimits
public import SheafCohomology.AbelianForget.ConePullbackCocone
public import SheafCohomology.LimitConstruction
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

/-!
# Cofiltered limits of additive sheafed spaces after forgetting coefficients

For a same-universe filtered index category `J`, forgetting the abelian-group
structure of the sheaves preserves the native limit of a diagram indexed by
`Jᵒᵖ`. The proof uses the accepted native cone construction and its actual
projection-mate cocone, and the filtered-colimit theorem for sheaves on the
underlying space. The index must be filtered: forgetting additive structure
does not generally preserve the initial sheaf of an empty native limit.

Original additive proof: Formal Frontier Agents; contributor history and
related adaptation are described in `docs/CREDITS.md`.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Forgetting coefficients and transporting the inverse-image diagram preserves
the colimit of the actual projection-mate cocone of an additive native cone. -/
noncomputable def isColimit_conePullbackCocone_underlying
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (C : Cone S)
    (hK : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :
    IsColimit (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone C)) := by
  let D := SheafedSpace.conePullback AddCommGrpCat.{v} S
    ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)
  let F := underlyingSheaf (C.pt : TopCat)
  have hMapped : IsColimit
      (F.mapCocone (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :=
    Classical.choice ((preservesFilteredSheafColimit (C.pt : TopCat) D).preserves hK)
  have hPre := (IsColimit.precomposeHomEquiv
    (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)) _).symm hMapped
  refine hPre.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ ?_))
  change (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)).hom.app i ≫
      (underlyingSheaf (C.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C).ι.app i) =
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone C)).ι.app i
  exact (conePullbackCocone_forget_ι S C i).symm

/-- A constructed native limit above a given limiting space cone remains
limiting after forgetting the abelian-group structure of its sheaf. -/
theorem preservesLimit_fromSpaceCone
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c)
    [HasWeakSheafify (Opens.grothendieckTopology c.pt) AddCommGrpCat.{v}] :
    PreservesLimit S underlying := by
  let K := SheafedSpace.conePullbackColimitCocone AddCommGrpCat.{v} S c
  let C := (SheafedSpace.limitConeOfSpaceCone AddCommGrpCat.{v} S c hc).cone
  have hK : IsColimit K :=
    SheafedSpace.conePullbackColimitCocone_isColimit AddCommGrpCat.{v} S c
  have hC : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C) := by
    change IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S
      (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K))
    refine hK.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ ?_))
    change K.ι.app i = SheafedSpace.sheafMate AddCommGrpCat.{v}
      ((SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K).π.app (op i))
    exact (SheafedSpace.coneOfPullbackCocone_π_mate AddCommGrpCat.{v}
      S c K (op i)).symm
  have hBase : IsLimit ((SheafedSpace.forget (Type v)).mapCone
      (underlying.mapCone C)) := by
    rw [underlying_mapCone_forget S C]
    rw [SheafedSpace.limitConeOfSpaceCone_forget AddCommGrpCat.{v} S c hc]
    exact hc
  have hSheaf := isColimit_conePullbackCocone_underlying S C hC
  have hType : IsLimit (underlying.mapCone C) :=
    SheafedSpace.isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
      (Type v) (S ⋙ underlying) (underlying.mapCone C) hBase hSheaf
  exact preservesLimit_of_preserves_limit_cone
    (SheafedSpace.limitConeOfSpaceCone AddCommGrpCat.{v} S c hc).isLimit hType

/-- The native coefficient-forgetting functor preserves every same-universe
cofiltered limit of additive sheafed spaces indexed by `Jᵒᵖ`. -/
theorem preservesCofilteredLimit
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) : PreservesLimit S underlying := by
  let c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}) :=
    limit.cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})
  let hc : IsLimit c := limit.isLimit (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})
  exact preservesLimit_fromSpaceCone S c hc

/-- A named shape-level witness, without a global preservation instance. -/
theorem preservesCofilteredLimitsOfShape :
    PreservesLimitsOfShape Jᵒᵖ underlying.{v} :=
  ⟨fun {S} ↦ preservesCofilteredLimit S⟩

end AlgebraicGeometry.SheafedSpace.AbelianForget
