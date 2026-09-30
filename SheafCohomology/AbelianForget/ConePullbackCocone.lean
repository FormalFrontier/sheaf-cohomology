/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.ConePullback
public import SheafCohomology.ConePullbackCocone

public section

/-!
# Forgetting the native inverse-image cocone

For a cone of additive sheafed spaces, the native Type-valued projection mates
agree with the forgotten additive projection mates after the canonical pullback
comparison. This identifies the induced maps from their ordinary colimits without
assuming that either cocone is colimiting.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat.Sheaf.AbelianForget

universe v vj wj

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

variable {J : Type wj} [Category.{vj} J]

/-- Mapping an actual native cone through the underlying sheafed-space functor
agrees strictly with forgetting its additive mapped cone. -/
theorem underlying_mapCone_forget (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S) :
    (SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c) =
      underlyingCone S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c) := by
  rfl

/-- The Type-valued leg of the actual native cone is precisely the additive
projection mate transported along the canonical pullback comparison. -/
theorem conePullbackCocone_forget_ι (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S) (i : J) :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) (underlying.mapCone c)).ι.app i =
      (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom.app i ≫
        (underlyingSheaf (c.pt : TopCat)).map
          ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app i) := by
  rw [SheafedSpace.conePullbackCocone_ι_app,
    SheafedSpace.conePullbackCocone_ι_app, conePullbackIso_hom_app]
  exact underlying_sheafMate (c.π.app (op i))

private theorem conePullbackCocone_forget_desc_canonical
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S)
    [hA : HasColimit (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))]
    [hAU : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)) ⋙
        underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt)]
    [hT : HasColimit (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      (underlyingCone S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)))] :
    (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom ≫
        colimit.post (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt)) ≫
      (underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt).map
        (colimit.desc (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c)) =
      colimit.desc (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
        (underlyingCone S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)))
        (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
          (underlying.mapCone c)) := by
  rw [Category.assoc, colimit.post_desc,
    @colimit.map_desc _ _ _ _ _ _ hAU hT
      ((underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt).mapCocone
        (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c))
      (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom]
  apply colimit.hom_ext (F := SheafedSpace.conePullback (Type v) (S ⋙ underlying)
    (underlyingCone S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)))
  intro i
  let K := (Cocone.precompose (conePullbackIso S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom).obj
        ((underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt).mapCocone
          (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c))
  have hfacL := @colimit.ι_desc _ _ _ _ _ hT K i
  have hfacR := @colimit.ι_desc _ _ _ _ _ hT
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)) i
  have hlegs : K.ι.app i =
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone c)).ι.app i := by
    change (conePullbackIso S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom.app i ≫
      (underlyingSheaf (c.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app i) = _
    exact (conePullbackCocone_forget_ι S c i).symm
  exact hfacL.trans (hlegs.trans hfacR.symm)

/-- The canonical comparison of ordinary colimits commutes with the maps to the
sheaf of the cone vertex. Only colimits of the actual native diagrams are assumed. -/
theorem conePullbackCocone_forget_desc (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone S)
    [hA : HasColimit (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))]
    [hAU : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)) ⋙
        underlyingSheaf (c.pt : TopCat))]
    [hT : HasColimit (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c)))] :
    (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom ≫
        colimit.post (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (underlyingSheaf (c.pt : TopCat))) ≫
      (underlyingSheaf (c.pt : TopCat)).map
        (colimit.desc (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c)) =
      colimit.desc (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
        ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c)))
        (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
          (underlying.mapCone c)) := by
  have hAUcanonical : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)) ⋙
      underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c).pt) := by
    change HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)) ⋙
      underlyingSheaf (c.pt : TopCat))
    exact hAU
  have hTcanonical : HasColimit (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      (underlyingCone S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))) := by
    rw [← underlying_mapCone_forget S c]
    exact hT
  exact @conePullbackCocone_forget_desc_canonical _ _ S c hA hAUcanonical hTcanonical

end AlgebraicGeometry.SheafedSpace.AbelianForget
