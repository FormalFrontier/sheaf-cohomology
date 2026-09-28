/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Formal Frontier worker-b Hive Task hive-request-4c216dbec01d4be3c9179c965656f0054d638fb8
-/
module
import SheafCohomology.NativeLimitGlobalSections

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeLimitGlobalSections

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v))
    (c : Cone (N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).map f))

include hstage htransition in
theorem nativeProjections_detect_coprojection_eq (i j : J)
    (s : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj i)
    (t : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj j)
    (h : AlgebraicGeometry.SheafedSpace.Γ.map
        ((AlgebraicGeometry.SheafedSpace.limitConeOfSpaceCone (Type v) N c hc).cone.π.app
          (op i)).op s =
      AlgebraicGeometry.SheafedSpace.Γ.map
        ((AlgebraicGeometry.SheafedSpace.limitConeOfSpaceCone (Type v) N c hc).cone.π.app
          (op j)).op t) :
    colimit.ι (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i s =
      colimit.ι (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) j t := by
  have hi := ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafedSpace.colimit_ι_nativeGlobalSectionsComparison N c hc i) s
  have hj := ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafedSpace.colimit_ι_nativeGlobalSectionsComparison N c hc j) t
  apply ((CategoryTheory.isIso_iff_bijective _).mp
    (AlgebraicGeometry.SheafedSpace.isIso_nativeGlobalSectionsComparison
      N c hc hstage htransition)).1
  exact hi.trans (h.trans hj.symm)

end SheafCohomologyExamples.NativeLimitGlobalSections
