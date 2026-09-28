/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Formal Frontier worker-a Hive Task hive-request-27d70680c0e69c147294098e3ac13b1c7092c0e1, UID bfe6acf9-1385-4602-a9b8-1e88f6908b1a
-/
module
import SheafCohomology.NativeCylinderLimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCylinderLimitAdditive

/-- The constructed additive restricted limit applied to an arbitrary cone
recovers its full native original-stage projection after the open inclusion. -/
private theorem lift_original_projection {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v}) (i0 : ι)
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

end SheafCohomologyExamples.NativeCylinderLimitAdditive
