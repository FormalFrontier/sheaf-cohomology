/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.NativeCylinderLimit

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCylinderLimit

/-- The constructed restricted limit, applied to an arbitrary restricted cone,
gives a lift whose composite with the open inclusion has the original native
projection equation. No limit on the restricted diagram is assumed. -/
private theorem lift_original_projection {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)) (i0 : ι)
    (m : Cone N) (hm : IsLimit m) (U0 : Opens (N.obj (op i0)))
    (t : Cone (restricted N i0 U0)) (i : Set.Ici i0) :
    let lift := (restrictedIsLimit N i0 m hm U0).lift t
    (lift ≫ m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding) ≫
        m.π.app (op i.1) =
      t.π.app (op i) ≫ (inclusion N i0 U0).app (op i) := by
  dsimp only
  have hfac := (restrictedIsLimit N i0 m hm U0).fac t (op i)
  change (restrictedIsLimit N i0 m hm U0).lift t ≫
      coneComponent N i0 m U0 i = t.π.app (op i) at hfac
  calc
    _ = (restrictedIsLimit N i0 m hm U0).lift t ≫
        (m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding ≫
          m.π.app (op i.1)) := Category.assoc _ _ _
    _ = (restrictedIsLimit N i0 m hm U0).lift t ≫
        (coneComponent N i0 m U0 i ≫ (inclusion N i0 U0).app (op i)) :=
          congrArg _ (coneComponent_fac N i0 m U0 i).symm
    _ = ((restrictedIsLimit N i0 m hm U0).lift t ≫ coneComponent N i0 m U0 i) ≫
        (inclusion N i0 U0).app (op i) := (Category.assoc _ _ _).symm
    _ = t.π.app (op i) ≫ (inclusion N i0 U0).app (op i) :=
          congrArg (· ≫ (inclusion N i0 U0).app (op i)) hfac

end SheafCohomologyExamples.NativeCylinderLimit
