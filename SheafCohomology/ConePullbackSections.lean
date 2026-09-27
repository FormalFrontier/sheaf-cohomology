/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.ConePullback
public import SheafCohomology.CompactOpenSections

public section

/-!
# Sections of a cone of inverse-image sheaves

The adjunction between inverse image and direct image transports sections across
arbitrary opens. At the top open these maps assemble into a transformation from
the global sections of a native sheafed-space diagram to sections of its
pullback to any cone over the underlying spaces.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe v

namespace SheafCohomology.ConePullbackSections

variable {X Y : TopCat.{v}} (f : X ⟶ Y)
variable {F : Y.Sheaf (Type v)} {G : X.Sheaf (Type v)}

/-- Transport a section through the actual inverse-image/direct-image adjunction. -/
def adjointSectionMap (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) : F.1.obj (op U) ⟶
      G.1.obj (op ((Opens.map f).obj U)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app (op U)

/-- After adjunction, a section may be restricted to any smaller inverse-image open. -/
def restrictedAdjointSectionMap
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    F.1.obj (op U) ⟶ G.1.obj (op V) :=
  adjointSectionMap f a U ≫ G.1.map (homOfLE hV).op

/-- The adjunction unit, restricted from the inverse image of an open. -/
def restrictedUnitSectionMap (F : Y.Sheaf (Type v))
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    F.1.obj (op U) ⟶
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.obj (op V) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app (op U) ≫
    ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hV).op

/-- The restricted unit is the literal adjunction unit followed by sheaf restriction. -/
theorem restrictedUnitSectionMap_eq_unit_comp (F : Y.Sheaf (Type v))
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    restrictedUnitSectionMap f F U V hV =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app (op U) ≫
        ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hV).op := by
  rfl

/-- An adjoint section map respects restriction on the source open. -/
theorem restrictedAdjointSectionMap_restrict_source
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    {U U' : Opens Y} (hU : U' ≤ U) {V : Opens X}
    (hV : V ≤ (Opens.map f).obj U') :
    restrictedAdjointSectionMap f a U V
        (hV.trans (Opens.comap_mono f.hom hU)) =
      F.1.map (homOfLE hU).op ≫ restrictedAdjointSectionMap f a U' V hV := by
  let hW : (Opens.map f).obj U' ≤ (Opens.map f).obj U :=
    Opens.comap_mono f.hom hU
  have hopen : (homOfLE (hV.trans hW)).op =
      (homOfLE hW).op ≫ (homOfLE hV).op := Subsingleton.elim _ _
  have hpush :
      (((TopCat.Sheaf.pushforward (Type v) f).obj G).1.map (homOfLE hU).op) =
        G.1.map (homOfLE hW).op := by
    change G.1.map ((Opens.map f).op.map (homOfLE hU).op) = _
    exact congrArg G.1.map (Subsingleton.elim _ _)
  unfold restrictedAdjointSectionMap adjointSectionMap
  rw [hopen, G.1.map_comp, ← hpush]
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.naturality_assoc
    (homOfLE hU).op (G.1.map (homOfLE hV).op) |>.symm

/-- An adjoint section map respects restriction on the target open. -/
theorem restrictedAdjointSectionMap_restrict_target
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) {V V' : Opens X}
    (hV : V ≤ (Opens.map f).obj U) (hV' : V' ≤ V) :
    restrictedAdjointSectionMap f a U V' (hV'.trans hV) =
      restrictedAdjointSectionMap f a U V hV ≫ G.1.map (homOfLE hV').op := by
  unfold restrictedAdjointSectionMap
  rw [show (homOfLE (hV'.trans hV)).op =
    (homOfLE hV).op ≫ (homOfLE hV').op from Subsingleton.elim _ _]
  rw [G.1.map_comp, Category.assoc]

/-- At a given open, adjunction factors through its unit and the actual sheaf morphism. -/
theorem adjointSectionMap_eq_unit_comp
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G) (U : Opens Y) :
    adjointSectionMap f a U =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app (op U) ≫
        a.hom.app (op ((Opens.map f).obj U)) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv_unit
    (f := a)
  exact congrArg (fun e ↦ e.hom.app (op U)) h

/-- The same unit factorization after restricting to a smaller inverse-image open. -/
theorem restrictedAdjointSectionMap_eq_unit_comp
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    restrictedAdjointSectionMap f a U V hV =
      restrictedUnitSectionMap f F U V hV ≫ a.hom.app (op V) := by
  unfold restrictedAdjointSectionMap restrictedUnitSectionMap
  rw [adjointSectionMap_eq_unit_comp]
  have hnat := a.hom.naturality (homOfLE hV).op
  simp only [Category.assoc]
  exact congrArg (fun e ↦
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
      (op U) ≫ e) hnat.symm

/-- The unrestricted adjoint of a composite pullback is the composite of its adjoints. -/
private theorem adjoint_comp {W : TopCat.{v}} (q : W ⟶ X)
    {H : W.Sheaf (Type v)}
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (b : (TopCat.Sheaf.pullback (Type v) q).obj G ⟶ H) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (q ≫ f)).homEquiv F H
      (TopCat.Sheaf.pullbackCompInv (Type v) q f F ≫
        (TopCat.Sheaf.pullback (Type v) q).map a ≫ b) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a ≫
        (TopCat.Sheaf.pushforward (Type v) f).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv G H b) := by
  let adjComp := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q)
  let adjDirect : TopCat.Sheaf.pullback (Type v) (q ≫ f) ⊣
      (TopCat.Sheaf.pushforward (Type v) q ⋙
        TopCat.Sheaf.pushforward (Type v) f) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (q ≫ f)
  change adjDirect.homEquiv F H
      ((Adjunction.leftAdjointUniq adjComp adjDirect).inv.app F ≫
        ((TopCat.Sheaf.pullback (Type v) q).map a ≫ b)) = _
  rw [adjDirect.homEquiv_naturality_right]
  rw [Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← adjComp.homEquiv_unit]
  rw [Adjunction.comp_homEquiv]
  change
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F
      ((TopCat.Sheaf.pushforward (Type v) q).obj H))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv
        ((TopCat.Sheaf.pullback (Type v) f).obj F) H)
        ((TopCat.Sheaf.pullback (Type v) q).map a ≫ b)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G) a ≫
        (TopCat.Sheaf.pushforward (Type v) f).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv G H) b)
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv_naturality_left]
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv_naturality_right]

/-- Adjunction sends the published triangle morphism to the two-stage unit transport. -/
theorem triangleMap_adjoint {W : TopCat.{v}} (q : W ⟶ X)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (q ≫ f)).homEquiv F
        ((TopCat.Sheaf.pullback (Type v) q).obj G)
        (SheafedSpace.triangleMap (Type v) (rfl : q ≫ f = q ≫ f) a) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a ≫
        (TopCat.Sheaf.pushforward (Type v) f).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G) := by
  have hunit :
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv G
          ((TopCat.Sheaf.pullback (Type v) q).obj G)
            (𝟙 ((TopCat.Sheaf.pullback (Type v) q).obj G)) =
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G := by
    have h := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv_unit
      (f := 𝟙 ((TopCat.Sheaf.pullback (Type v) q).obj G))
    rw [(TopCat.Sheaf.pushforward (Type v) q).map_id] at h
    exact h.trans (Category.comp_id _)
  have htri : SheafedSpace.triangleMap (Type v) (rfl : q ≫ f = q ≫ f) a =
      TopCat.Sheaf.pullbackCompInv (Type v) q f F ≫
        (TopCat.Sheaf.pullback (Type v) q).map a := by
    rfl
  rw [htri]
  simpa only [Category.comp_id, hunit] using
    adjoint_comp f q a (𝟙 ((TopCat.Sheaf.pullback (Type v) q).obj G))

/-- An inclusion into the inverse image of a nested open is induced by the triangle. -/
theorem triangleOpen_le {W : TopCat.{v}}
    {p : W ⟶ Y} {q : W ⟶ X} (h : q ≫ f = p)
    {U : Opens Y} {V : Opens X} {T : Opens W}
    (hV : V ≤ (Opens.map f).obj U) (hT : T ≤ (Opens.map q).obj V) :
    T ≤ (Opens.map p).obj U := by
  intro point hpoint
  change p point ∈ U
  rw [← ConcreteCategory.congr_hom h point]
  exact hV (hT hpoint)

/-- Triangle transport of sections holds over arbitrary nested source and target opens. -/
theorem restrictedAdjointSectionMap_triangle
    {W : TopCat.{v}} {p : W ⟶ Y} {q : W ⟶ X}
    (h : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G)
    (U : Opens Y) (V : Opens X) (T : Opens W)
    (hV : V ≤ (Opens.map f).obj U) (hT : T ≤ (Opens.map q).obj V) :
    restrictedAdjointSectionMap p (SheafedSpace.triangleMap (Type v) h a)
        U T (triangleOpen_le f h hV hT) =
      restrictedAdjointSectionMap f a U V hV ≫
        restrictedUnitSectionMap q G V T hT := by
  subst p
  have hmate := triangleMap_adjoint f q a
  have happ := congrArg (fun m ↦ m.hom.app (op U)) hmate
  unfold restrictedAdjointSectionMap restrictedUnitSectionMap adjointSectionMap
  rw [happ]
  have hnat :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.naturality
      (homOfLE hV).op
  let hW : (Opens.map q).obj V ≤
      (Opens.map q).obj ((Opens.map f).obj U) :=
    Opens.comap_mono q.hom hV
  have hrestrict :
      ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map
          (homOfLE (triangleOpen_le f (rfl : q ≫ f = q ≫ f) hV hT)).op =
        ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map (homOfLE hW).op ≫
          ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map (homOfLE hT).op := by
    rw [← Functor.map_comp]
    exact congrArg ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map
      (Subsingleton.elim _ _)
  change
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
        (op U) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
        (op ((Opens.map f).obj U)) ≫
      ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map
        (homOfLE (triangleOpen_le f (rfl : q ≫ f = q ≫ f) hV hT)).op =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
        (op U) ≫ G.1.map (homOfLE hV).op ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
        (op V) ≫ ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map
          (homOfLE hT).op
  apply ConcreteCategory.hom_ext
  intro localSection
  change
    ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map
        (homOfLE (triangleOpen_le f (rfl : q ≫ f = q ≫ f) hV hT)).op
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
        (op ((Opens.map f).obj U))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
          (op U) localSection)) =
    ((TopCat.Sheaf.pullback (Type v) q).obj G).1.map (homOfLE hT).op
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
        (op V)
        (G.1.map (homOfLE hV).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
            (op U) localSection)))
  have hfirst := congrArg (fun e ↦ e
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
        (op ((Opens.map f).obj U))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
          (op U) localSection))) hrestrict
  have hsecond := congrArg (fun e ↦ e
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv F G a).hom.app
        (op U) localSection)) hnat
  exact hfirst.trans (congrArg
    (((TopCat.Sheaf.pullback (Type v) q).obj G).1.map (homOfLE hT).op) hsecond.symm)

/-- At the maximal opens the triangle is the expected two-stage section transport. -/
theorem adjointSectionMap_triangle_top
    {W : TopCat.{v}} {p : W ⟶ Y} {q : W ⟶ X}
    (h : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G) :
    adjointSectionMap p (SheafedSpace.triangleMap (Type v) h a) ⊤ =
      adjointSectionMap f a ⊤ ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
          (op (⊤ : Opens X)) := by
  have hV : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤ := by simp
  have hT : (⊤ : Opens W) ≤ (Opens.map q).obj ⊤ := by simp
  have htriangle := restrictedAdjointSectionMap_triangle f h a ⊤ ⊤ ⊤ hV hT
  simpa [restrictedAdjointSectionMap, restrictedUnitSectionMap,
    adjointSectionMap] using htriangle

/-- Explicitly, the projection unit followed by the native triangle map equals
the adjoint stage transition followed by the other projection unit at the top. -/
theorem triangleMap_unit_top
    {W : TopCat.{v}} {p : W ⟶ Y} {q : W ⟶ X}
    (h : q ≫ f = p)
    (a : (TopCat.Sheaf.pullback (Type v) f).obj F ⟶ G) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) p).unit.app F).hom.app
        (op (⊤ : Opens Y)) ≫
      (SheafedSpace.triangleMap (Type v) h a).hom.app (op (⊤ : Opens W)) =
      adjointSectionMap f a ⊤ ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app G).hom.app
          (op (⊤ : Opens X)) := by
  have hfactor := adjointSectionMap_eq_unit_comp p
    (SheafedSpace.triangleMap (Type v) h a) ⊤
  have htriangle := adjointSectionMap_triangle_top f h a
  simpa only [Opens.map_top] using hfactor.symm.trans htriangle

end SheafCohomology.ConePullbackSections

namespace SheafCohomology.ConePullbackSections

variable {J : Type v} [SmallCategory J]

/-- Global stage sections map to sections of the stage pullbacks on any cone vertex. -/
@[expose] def coneSections (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) :
    N.rightOp ⋙ SheafedSpace.Γ ⟶
      SheafedSpace.conePullback (Type v) N c ⋙
        SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt) where
  app i :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
        (op (⊤ : Opens (N.obj (op i) : TopCat)))
  naturality := by
    intro i j arrow
    have hmate := SheafedSpace.sheafMate_adjoint (Type v) (N.map arrow.op)
    have htriangle := adjointSectionMap_triangle_top
      (N.map arrow.op).hom.base (c.w arrow.op)
        (SheafedSpace.sheafMate (Type v) (N.map arrow.op))
    have happ := congrArg (fun m ↦ m.hom.app
      (op (⊤ : Opens (N.obj (op i) : TopCat)))) hmate
    change
      (N.map arrow.op).hom.c.app (op (⊤ : Opens (N.obj (op i) : TopCat))) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app (op ⊤) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op ⊤) ≫
        (SheafedSpace.triangleMap (Type v) (c.w arrow.op)
          (SheafedSpace.sheafMate (Type v) (N.map arrow.op))).hom.app (op ⊤)
    have htransport := htriangle.trans (congrArg (fun m ↦ m ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app (op ⊤)) happ)
    have hfactor := adjointSectionMap_eq_unit_comp
      (c.π.app (op i))
      (SheafedSpace.triangleMap (Type v) (c.w arrow.op)
        (SheafedSpace.sheafMate (Type v) (N.map arrow.op))) ⊤
    exact htransport.symm.trans hfactor

/-- Each component is exactly the unit of the native inverse-image adjunction. -/
theorem coneSections_app (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (i : J) :
    (coneSections N c).app i =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i) : TopCat))) := rfl

/-- The induced colimit map agrees with the projection unit on every stage leg. -/
theorem colimit_ι_colimMap_coneSections
    (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v)))
    [HasColimit (N.rightOp ⋙ SheafedSpace.Γ)]
    [HasColimit (SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt))]
    (i : J) :
    colimit.ι (N.rightOp ⋙ SheafedSpace.Γ) i ≫ colimMap (coneSections N c) =
      (coneSections N c).app i ≫
        colimit.ι (SheafedSpace.conePullback (Type v) N c ⋙
          SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)) i :=
  ι_colimMap (coneSections N c) i

end SheafCohomology.ConePullbackSections
