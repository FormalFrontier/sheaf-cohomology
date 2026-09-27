/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullbackSections

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe v

namespace SheafCohomologyExamples.ConePullbackSections

/-- A client transports through a native sheaf triangle on three nested arbitrary opens. -/
theorem nestedOpens
    {W X Y : TopCat.{v}} {p : W ⟶ X} {q : W ⟶ Y} {f : Y ⟶ X}
    {F : X.Sheaf (Type v)} {G : Y.Sheaf (Type v)}
    (h : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens X) (V : Opens Y) (T : Opens W)
    (hV : V ≤ (Opens.map f).obj U) (hT : T ≤ (Opens.map q).obj V) :
    SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap p
        (SheafedSpace.triangleMap (Type v) h a) U T
        (SheafCohomology.ConePullbackSections.triangleOpen_le f h hV hT) =
      SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap f a U V hV ≫
        SheafCohomology.ConePullbackSections.restrictedUnitSectionMap q G V T hT :=
  SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_triangle
    f h a U V T hV hT

/-- Literal units and restrictions compose through the native triangle on arbitrary opens. -/
theorem literalUnitsTriangle
    {W X Y : TopCat.{v}} {p : W ⟶ Y} {q : W ⟶ X} {f : X ⟶ Y}
    {F : Y.Sheaf (Type v)} {G : X.Sheaf (Type v)}
    (h : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) (V : Opens X) (T : Opens W)
    (hV : V ≤ (Opens.map f).obj U) (hT : T ≤ (Opens.map q).obj V) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op U) ≫ ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hV).op) ≫
      a.hom.app (op V) ≫
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
          (op V) ≫ ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map (homOfLE hT).op) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) p).unit.app F).hom.app
        (op U) ≫ ((TopCat.Sheaf.pullback (Type v) p).obj F).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le f h hV hT)).op) ≫
        (SheafedSpace.triangleMap (Type v) h a).hom.app (op T) := by
  calc
    _ = SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap f a U V hV ≫
        SheafCohomology.ConePullbackSections.restrictedUnitSectionMap q G V T hT := by
          rw [SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_eq_unit_comp,
            SheafCohomology.ConePullbackSections.restrictedUnitSectionMap_eq_unit_comp,
            SheafCohomology.ConePullbackSections.restrictedUnitSectionMap_eq_unit_comp]
          simp only [Category.assoc]
    _ = SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap p
        (SheafedSpace.triangleMap (Type v) h a) U T
        (SheafCohomology.ConePullbackSections.triangleOpen_le f h hV hT) :=
          (SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_triangle
            f h a U V T hV hT).symm
    _ = _ := by
      rw [SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_eq_unit_comp,
        SheafCohomology.ConePullbackSections.restrictedUnitSectionMap_eq_unit_comp]

variable {J : Type v} [SmallCategory J]

/-- A client sees the projection unit over any cone, with no limiting assumption. -/
theorem arbitraryConeComponent (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (i : J) :
    (SheafCohomology.ConePullbackSections.coneSections N c).app i =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i) : TopCat))) :=
  SheafCohomology.ConePullbackSections.coneSections_app N c i

/-- Naturality is the native mate and actual cone-pullback triangle map. -/
theorem arbitraryConeNaturality (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v)))
    {i j : J} (arrow : i ⟶ j) :
    (N.map arrow.op).hom.c.app (op (⊤ : Opens (N.obj (op i) : TopCat))) ≫
        (SheafCohomology.ConePullbackSections.coneSections N c).app j =
      (SheafCohomology.ConePullbackSections.coneSections N c).app i ≫
        (SheafedSpace.triangleMap (Type v) (c.w arrow.op)
          (SheafedSpace.sheafMate (Type v) (N.map arrow.op))).hom.app (op ⊤) := by
  exact (SheafCohomology.ConePullbackSections.coneSections N c).naturality arrow

/-- The ordinary `colimMap` of the native transformation has the expected stage legs. -/
theorem arbitraryConeColimitLeg (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v)))
    [HasColimit (N.rightOp ⋙ SheafedSpace.Γ)]
    [HasColimit (SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt))]
    (i : J) :
    colimit.ι (N.rightOp ⋙ SheafedSpace.Γ) i ≫
        colimMap (SheafCohomology.ConePullbackSections.coneSections N c) =
      (SheafCohomology.ConePullbackSections.coneSections N c).app i ≫
        colimit.ι (SheafedSpace.conePullback (Type v) N c ⋙
          SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)) i :=
  SheafCohomology.ConePullbackSections.colimit_ι_colimMap_coneSections N c i

end SheafCohomologyExamples.ConePullbackSections
