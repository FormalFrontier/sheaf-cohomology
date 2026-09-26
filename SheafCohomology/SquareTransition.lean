/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.PullbackCoherence

public section

set_option warningAsError true

/-!
# Transitions across commuting squares of sheaves

For a commuting square `p ≫ fi = fj ≫ q`, a map from the pullback of a
sheaf along `p` induces a map between the corresponding pushforwards along
`fi` and `fj`. The comparison uses the canonical composite-pullback
isomorphisms, equality transport, and the counit of `fi`. Its adjoint across
`q` is the pushforward of the original adjoint followed by the forward strict
pushforward comparison. No assumption about the maps of spaces is needed.

The coefficient assumptions and universes are those of the native sheaf
pullback adjunction: the universe of space carriers and morphisms is also the
coefficient carrier universe; the coefficient object universe is independent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace TopCat.Sheaf.SquareTransition

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {Xj Xi Yj Yi : TopCat.{w}}

/-- The adjoint of a transition along a single map of spaces. -/
def adjoint (p : Xj ⟶ Xi) {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    F ⟶ (pushforward A p).obj G :=
  (pullbackPushforwardAdjunction A p).homEquiv F G a

/-- Compute the adjoint via the native pullback/pushforward hom-bijection. -/
theorem adjoint_eq_homEquiv (p : Xj ⟶ Xi) {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    adjoint A p a = (pullbackPushforwardAdjunction A p).homEquiv F G a := by
  unfold adjoint
  rfl

/-- Canonical pullback transition along an identity map. -/
def identity (F : Xi.Sheaf A) :
    (pullback A (𝟙 Xi)).obj F ⟶ F :=
  pullbackIdHom A Xi F

/-- Pullback of two consecutive stage maps, retaining the canonical inverse
composite-pullback comparison rather than identifying the sources by fiat. -/
def composite {Xk : TopCat.{w}} (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A} {H : Xk.Sheaf A}
    (aij : (pullback A pij).obj F ⟶ G)
    (ajk : (pullback A pjk).obj G ⟶ H) :
    (pullback A (pjk ≫ pij)).obj F ⟶ H :=
  pullbackCompInv A pjk pij F ≫ (pullback A pjk).map aij ≫ ajk

/-- Transport between pullback functors for equal maps, in the contravariant
direction. -/
def pullbackEqIso {a b : Xj ⟶ Yi} (h : a = b) :
    pullback A b ≅ pullback A a := by
  subst b
  exact Iso.refl _

theorem pullbackEqIso_hom {a b : Xj ⟶ Yi} (h : a = b) :
    (pullbackEqIso A h).hom = eqToHom (by rw [h]) := by
  subst b
  rfl

/-- Forward equality transport for strictly composable pushforwards. -/
def pushforwardEqIso {a b : Xj ⟶ Yi} (h : a = b) :
    pushforward A a ≅ pushforward A b := by
  subst b
  exact Iso.refl _

omit [HasColimits A] [HasLimits A] in
theorem pushforwardEqIso_hom {a b : Xj ⟶ Yi} (h : a = b) :
    (pushforwardEqIso A h).hom =
      eqToHom (congrArg (pushforward A) h) := by
  subst b
  rfl

/-- The pushforward of a composite is definitionally the composite of the
pushforwards, but the comparison records both presentations. -/
def pushforwardCompIso {Xk : TopCat.{w}} (f : Xk ⟶ Xj)
    (g : Xj ⟶ Yi) :
    pushforward A f ⋙ pushforward A g ≅ pushforward A (f ≫ g) := by
  change pushforward A (f ≫ g) ≅ pushforward A (f ≫ g)
  exact Iso.refl _

/-- The pullback comparison across the square as a natural isomorphism. -/
def pullbackSquareIso (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    pullback A q ⋙ pullback A fj ≅
      pullback A fi ⋙ pullback A p :=
  pullbackCompIso A fj q ≪≫ pullbackEqIso A h ≪≫
    (pullbackCompIso A p fi).symm

/-- The literal square comparison, including the equality transport. -/
def pullbackComparison (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    (G : Yi.Sheaf A) :
    (pullback A fj).obj ((pullback A q).obj G) ⟶
      (pullback A p).obj ((pullback A fi).obj G) :=
  (pullbackCompIso A fj q).hom.app G ≫
    eqToHom (by rw [h]) ≫ (pullbackCompIso A p fi).inv.app G

theorem pullbackComparison_eq_iso_app (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    (G : Yi.Sheaf A) :
    pullbackComparison A p q fi fj h G =
      (pullbackSquareIso A p q fi fj h).hom.app G := by
  simp [pullbackComparison, pullbackSquareIso, pullbackEqIso_hom]

/-- The mate of the pullback comparison across a commuting square. -/
def pushforwardSquareMateIso (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    pushforward A p ⋙ pushforward A fi ≅
      pushforward A fj ⋙ pushforward A q :=
  conjugateIsoEquiv
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    ((pullbackPushforwardAdjunction A q).comp
      (pullbackPushforwardAdjunction A fj))
    (pullbackSquareIso A p q fi fj h)

/-- The forward strict pushforward comparison used by the transition law. -/
def pushforwardSquareIso (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    pushforward A p ⋙ pushforward A fi ≅
      pushforward A fj ⋙ pushforward A q :=
  pushforwardCompIso A p fi ≪≫ pushforwardEqIso A h ≪≫
    (pushforwardCompIso A fj q).symm

omit [HasColimits A] [HasLimits A] in
theorem pushforwardSquareIso_hom_eq (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    (pushforwardSquareIso A p q fi fj h).hom =
      eqToHom (congrArg (pushforward A) h) := by
  unfold pushforwardSquareIso
  rw [Iso.trans_hom, Iso.trans_hom, pushforwardEqIso_hom]
  change (𝟙 _) ≫ eqToHom (congrArg (pushforward A) h) ≫ (𝟙 _) = _
  simp

private theorem pullbackCompIso_inv_mate {Xk : TopCat.{w}}
    (f : Xk ⟶ Xj) (g : Xj ⟶ Yi) :
    conjugateEquiv
      ((pullbackPushforwardAdjunction A g).comp
        (pullbackPushforwardAdjunction A f))
      (pullbackPushforwardAdjunction A (f ≫ g))
      (pullbackCompIso A f g).inv = (pushforwardCompIso A f g).hom := by
  change conjugateEquiv
    ((pullbackPushforwardAdjunction A g).comp
      (pullbackPushforwardAdjunction A f))
    (pullbackPushforwardAdjunction A (f ≫ g))
    (Adjunction.leftAdjointCompIso
      (pullbackPushforwardAdjunction A g)
      (pullbackPushforwardAdjunction A f)
      (pullbackPushforwardAdjunction A (f ≫ g))
      (pushforwardCompIso A f g)).inv =
      (pushforwardCompIso A f g).hom
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (pullbackPushforwardAdjunction A g)
    (pullbackPushforwardAdjunction A f)
    (pullbackPushforwardAdjunction A (f ≫ g))
    (pushforwardCompIso A f g)

private theorem pullbackCompIso_hom_mate {Xk : TopCat.{w}}
    (f : Xk ⟶ Xj) (g : Xj ⟶ Yi) :
    conjugateEquiv (pullbackPushforwardAdjunction A (f ≫ g))
      ((pullbackPushforwardAdjunction A g).comp
        (pullbackPushforwardAdjunction A f))
      (pullbackCompIso A f g).hom = (pushforwardCompIso A f g).inv := by
  have hcomm := conjugateEquiv_comm
    (pullbackPushforwardAdjunction A (f ≫ g))
    ((pullbackPushforwardAdjunction A g).comp
      (pullbackPushforwardAdjunction A f))
    (Iso.inv_hom_id_assoc (pullbackCompIso A f g) (𝟙 _))
  rw [pullbackCompIso_inv_mate] at hcomm
  rw [← cancel_mono (pushforwardCompIso A f g).hom]
  simpa using hcomm

private theorem mapEqIso_mate {a b : Xj ⟶ Yi} (h : a = b) :
    conjugateIsoEquiv (pullbackPushforwardAdjunction A a)
      (pullbackPushforwardAdjunction A b) (pullbackEqIso A h) =
      pushforwardEqIso A h := by
  subst b
  apply Iso.ext
  change conjugateEquiv (pullbackPushforwardAdjunction A a)
    (pullbackPushforwardAdjunction A a) (𝟙 _) = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual mate of the canonical pullback square is the forward strict
pushforward comparison (and not its inverse). -/
theorem pushforwardSquareMateIso_eq (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q) :
    pushforwardSquareMateIso A p q fi fj h =
      pushforwardSquareIso A p q fi fj h := by
  apply Iso.ext
  change conjugateEquiv
      ((pullbackPushforwardAdjunction A fi).comp
        (pullbackPushforwardAdjunction A p))
      ((pullbackPushforwardAdjunction A q).comp
        (pullbackPushforwardAdjunction A fj))
      (pullbackSquareIso A p q fi fj h).hom =
    (pushforwardSquareIso A p q fi fj h).hom
  change conjugateEquiv
      ((pullbackPushforwardAdjunction A fi).comp
        (pullbackPushforwardAdjunction A p))
      ((pullbackPushforwardAdjunction A q).comp
        (pullbackPushforwardAdjunction A fj))
      ((pullbackCompIso A fj q).hom ≫
        (pullbackEqIso A h).hom ≫ (pullbackCompIso A p fi).inv) =
    (pushforwardCompIso A p fi).hom ≫
      (pushforwardEqIso A h).hom ≫ (pushforwardCompIso A fj q).inv
  rw [← conjugateEquiv_comp
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    (pullbackPushforwardAdjunction A (fj ≫ q))
    ((pullbackPushforwardAdjunction A q).comp
      (pullbackPushforwardAdjunction A fj))]
  rw [← conjugateEquiv_comp
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    (pullbackPushforwardAdjunction A (p ≫ fi))
    (pullbackPushforwardAdjunction A (fj ≫ q))]
  have hmid := congrArg Iso.hom (mapEqIso_mate A h)
  change conjugateEquiv
    (pullbackPushforwardAdjunction A (p ≫ fi))
    (pullbackPushforwardAdjunction A (fj ≫ q))
    (pullbackEqIso A h).hom = (pushforwardEqIso A h).hom at hmid
  rw [pullbackCompIso_inv_mate, hmid, pullbackCompIso_hom_mate]
  exact Category.assoc _ _ _

/-- The counit construction defining the square-induced transition. -/
def mate (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    (pullback A fj).obj ((pullback A q).obj ((pushforward A fi).obj F)) ⟶ G :=
  pullbackComparison A p q fi fj h ((pushforward A fi).obj F) ≫
    (pullback A p).map ((pullbackPushforwardAdjunction A fi).counit.app F) ≫ a

/-- Square transition induced by an arbitrary stage morphism. -/
def transition (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    (pullback A q).obj ((pushforward A fi).obj F) ⟶
      (pushforward A fj).obj G :=
  (pullbackPushforwardAdjunction A fj).homEquiv _ _
    (mate A p q fi fj h a)

theorem transition_adjoint (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    ((pullbackPushforwardAdjunction A fj).homEquiv _ _).symm
      (transition A p q fi fj h a) = mate A p q fi fj h a :=
  Equiv.symm_apply_apply _ _

theorem transition_proof_irrel (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj)
    (h h' : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    transition A p q fi fj h a = transition A p q fi fj h' a := by
  rw [Subsingleton.elim h h']

/-- The native square-mate law: the `q`-adjoint of the literal transition
is the `fi`-pushforward of the `p`-adjoint, then the *forward* strict square
comparison. -/
theorem adjoint_transition (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) :
    adjoint A q (transition A p q fi fj h a) =
      (pushforward A fi).map (adjoint A p a) ≫
        (pushforwardSquareIso A p q fi fj h).hom.app G := by
  unfold adjoint transition
  change
    (Equiv.trans
      ((pullbackPushforwardAdjunction A fj).homEquiv _ _)
      ((pullbackPushforwardAdjunction A q).homEquiv _ _))
      (mate A p q fi fj h a) = _
  have hcomp := congrFun (congrFun
    (Adjunction.comp_homEquiv
      (pullbackPushforwardAdjunction A q)
      (pullbackPushforwardAdjunction A fj))
    ((pushforward A fi).obj F)) G
  rw [← hcomp]
  simp only [Adjunction.homEquiv_unit]
  have hmate := congrArg Iso.hom
    (pushforwardSquareMateIso_eq A p q fi fj h)
  change conjugateEquiv
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    ((pullbackPushforwardAdjunction A q).comp
      (pullbackPushforwardAdjunction A fj))
    (pullbackSquareIso A p q fi fj h).hom =
      (pushforwardSquareIso A p q fi fj h).hom at hmate
  have hmate_app := congr_app hmate G
  change (conjugateEquiv
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    ((pullbackPushforwardAdjunction A q).comp
      (pullbackPushforwardAdjunction A fj))
    (pullbackSquareIso A p q fi fj h).hom).app G =
      (pushforwardSquareIso A p q fi fj h).hom.app G at hmate_app
  rw [← hmate_app]
  rw [mate, pullbackComparison_eq_iso_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc]
  rw [← CategoryTheory.unit_conjugateEquiv]
  rw [Category.assoc]
  erw [← Functor.map_comp]
  rw [← (conjugateEquiv
    ((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p))
    ((pullbackPushforwardAdjunction A q).comp
      (pullbackPushforwardAdjunction A fj))
    (pullbackSquareIso A p q fi fj h).hom).naturality]
  rw [← Category.assoc]
  change
    ((((pullbackPushforwardAdjunction A fi).comp
      (pullbackPushforwardAdjunction A p)).homEquiv _ _)
        ((pullback A p).map
          ((pullbackPushforwardAdjunction A fi).counit.app F) ≫ a)) ≫ _ = _
  rw [Adjunction.comp_homEquiv]
  change
    ((pullbackPushforwardAdjunction A fi).homEquiv _ _
      ((pullbackPushforwardAdjunction A p).homEquiv _ _
        ((pullback A p).map
          ((pullbackPushforwardAdjunction A fi).counit.app F) ≫ a))) ≫ _ = _
  rw [(pullbackPushforwardAdjunction A p).homEquiv_naturality_left]
  rw [(pullbackPushforwardAdjunction A fi).homEquiv_naturality_right]
  have hcounit :
      ((pullbackPushforwardAdjunction A fi).homEquiv _ _)
        ((pullbackPushforwardAdjunction A fi).counit.app F) = 𝟙 _ := by
    rw [← (pullbackPushforwardAdjunction A fi).homEquiv_symm_id F]
    exact ((pullbackPushforwardAdjunction A fi).homEquiv _ _).apply_symm_apply (𝟙 _)
  rw [hcounit, Category.id_comp]
  rw [← Category.assoc]
  rw [← Functor.map_comp]
  rw [← Adjunction.homEquiv_unit]
  rfl

/-- Naturality of the square transition in its target sheaf. -/
theorem transition_comp (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf A} {G H : Xj.Sheaf A}
    (a : (pullback A p).obj F ⟶ G) (b : G ⟶ H) :
    transition A p q fi fj h (a ≫ b) =
      transition A p q fi fj h a ≫ (pushforward A fj).map b := by
  have hm : mate A p q fi fj h (a ≫ b) =
      mate A p q fi fj h a ≫ b := by
    simp [mate, Category.assoc]
  unfold transition
  rw [hm, (pullbackPushforwardAdjunction A fj).homEquiv_naturality_right]

/-- The canonical identity pullback transition adjoints to the identity. -/
theorem adjoint_identity (F : Xi.Sheaf A) :
    adjoint A (𝟙 Xi) (identity A F) = 𝟙 F := by
  let adjDirect : pullback A (𝟙 Xi) ⊣ 𝟭 (Xi.Sheaf A) :=
    pullbackPushforwardAdjunction A (𝟙 Xi)
  change adjDirect.homEquiv F F
    ((Adjunction.leftAdjointUniq Adjunction.id adjDirect).inv.app F) = 𝟙 F
  rw [Adjunction.leftAdjointUniq_inv_app]
  simpa using
    (Adjunction.homEquiv_leftAdjointUniq_hom_app adjDirect Adjunction.id F)

/-- Taking the adjoint of a composite of stage maps preserves its actual
native composite-pullback comparison. -/
theorem adjoint_composite {Xk : TopCat.{w}}
    (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A} {H : Xk.Sheaf A}
    (aij : (pullback A pij).obj F ⟶ G)
    (ajk : (pullback A pjk).obj G ⟶ H) :
    adjoint A (pjk ≫ pij) (composite A pjk pij aij ajk) =
      adjoint A pij aij ≫ (pushforward A pij).map (adjoint A pjk ajk) := by
  let adjComp := (pullbackPushforwardAdjunction A pij).comp
    (pullbackPushforwardAdjunction A pjk)
  let adjDirect : pullback A (pjk ≫ pij) ⊣
      (pushforward A pjk ⋙ pushforward A pij) :=
    pullbackPushforwardAdjunction A (pjk ≫ pij)
  change adjDirect.homEquiv F H
    ((Adjunction.leftAdjointUniq adjComp adjDirect).inv.app F ≫
      ((pullback A pjk).map aij ≫ ajk)) = _
  rw [adjDirect.homEquiv_naturality_right]
  rw [Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← adjComp.homEquiv_unit]
  rw [Adjunction.comp_homEquiv]
  change
    ((pullbackPushforwardAdjunction A pij).homEquiv F
      ((pushforward A pjk).obj H))
      (((pullbackPushforwardAdjunction A pjk).homEquiv
        ((pullback A pij).obj F) H)
        ((pullback A pjk).map aij ≫ ajk)) =
      ((pullbackPushforwardAdjunction A pij).homEquiv F G) aij ≫
      (pushforward A pij).map
        (((pullbackPushforwardAdjunction A pjk).homEquiv G H) ajk)
  rw [(pullbackPushforwardAdjunction A pjk).homEquiv_naturality_left]
  rw [(pullbackPushforwardAdjunction A pij).homEquiv_naturality_right]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The transition across an identity square sends the canonical
identity-pullback comparison to the corresponding identity comparison. -/
theorem transition_identity (fi : Xi ⟶ Yi) (F : Xi.Sheaf A) :
    transition A (𝟙 Xi) (𝟙 Yi) fi fi (by simp) (identity A F) =
      identity A ((pushforward A fi).obj F) := by
  apply ((pullbackPushforwardAdjunction A (𝟙 Yi)).homEquiv _ _).injective
  change adjoint A (𝟙 Yi)
    (transition A (𝟙 Xi) (𝟙 Yi) fi fi (by simp) (identity A F)) =
    adjoint A (𝟙 Yi) (identity A ((pushforward A fi).obj F))
  rw [adjoint_transition]
  change (pushforward A fi).map (adjoint A (𝟙 Xi) (identity A F)) ≫
    (pushforwardSquareIso A (𝟙 Xi) (𝟙 Yi) fi fi (by simp)).hom.app F = _
  have hsq : (pushforwardSquareIso A (𝟙 Xi) (𝟙 Yi) fi fi (by simp)).hom.app F =
      𝟙 ((pushforward A fi).obj F) := by
    rw [pushforwardSquareIso_hom_eq, eqToHom_app]
    apply eqToHom_refl
  rw [adjoint_identity, adjoint_identity, hsq]
  calc
    (pushforward A fi).map (𝟙 F) ≫ 𝟙 ((pushforward A fi).obj F) =
        (𝟙 ((pushforward A fi).obj F)) ≫ 𝟙 _ := by
      exact congrArg (· ≫ 𝟙 _) ((pushforward A fi).map_id F)
    _ = 𝟙 _ := Category.id_comp _

/-- Pasting two genuinely arbitrary square transitions agrees with the
transition of the pasted square, with native composite-pullback transport on
both sides. -/
theorem transition_composite
    {Xk Yk : TopCat.{w}} (pjk : Xk ⟶ Xj) (pij : Xj ⟶ Xi)
    (qjk : Yk ⟶ Yj) (qij : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (fk : Xk ⟶ Yk)
    (hij : pij ≫ fi = fj ≫ qij) (hjk : pjk ≫ fj = fk ≫ qjk)
    {F : Xi.Sheaf A} {G : Xj.Sheaf A} {H : Xk.Sheaf A}
    (aij : (pullback A pij).obj F ⟶ G)
    (ajk : (pullback A pjk).obj G ⟶ H) :
    transition A (pjk ≫ pij) (qjk ≫ qij) fi fk
      (by rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc])
      (composite A pjk pij aij ajk) =
    composite A qjk qij
      (transition A pij qij fi fj hij aij)
      (transition A pjk qjk fj fk hjk ajk) := by
  let hout : (pjk ≫ pij) ≫ fi = fk ≫ (qjk ≫ qij) := by
    rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc]
  rw [transition_proof_irrel A (pjk ≫ pij) (qjk ≫ qij) fi fk
    (show (pjk ≫ pij) ≫ fi = fk ≫ (qjk ≫ qij) by
      rw [Category.assoc, hij, ← Category.assoc, hjk, Category.assoc]) hout
    (composite A pjk pij aij ajk)]
  apply ((pullbackPushforwardAdjunction A (qjk ≫ qij)).homEquiv _ _).injective
  change adjoint A (qjk ≫ qij)
    (transition A (pjk ≫ pij) (qjk ≫ qij) fi fk hout
      (composite A pjk pij aij ajk)) =
    adjoint A (qjk ≫ qij)
      (composite A qjk qij
        (transition A pij qij fi fj hij aij)
        (transition A pjk qjk fj fk hjk ajk))
  rw [adjoint_transition, adjoint_composite, adjoint_composite]
  rw [adjoint_transition, adjoint_transition]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((pushforwardSquareIso A pij qij fi fj hij).hom.app G)]
  erw [← (pushforwardSquareIso A pij qij fi fj hij).hom.naturality]
  have hpaste :
      (pushforwardSquareIso A pij qij fi fj hij).hom.app
          ((pushforward A pjk).obj H) ≫
        (pushforward A qij).map
          ((pushforwardSquareIso A pjk qjk fj fk hjk).hom.app H) =
      (pushforwardSquareIso A (pjk ≫ pij) (qjk ≫ qij) fi fk hout).hom.app H := by
    simp only [pushforwardSquareIso_hom_eq, eqToHom_app]
    erw [eqToHom_map]
    erw [eqToHom_trans]
    rfl
  simp only [Category.assoc]
  erw [hpaste]
  erw [Functor.map_comp]
  erw [Functor.comp_map]
  rw [Category.assoc]
  rfl

#print axioms adjoint
#print axioms adjoint_eq_homEquiv
#print axioms identity
#print axioms composite
#print axioms pullbackEqIso
#print axioms pullbackEqIso_hom
#print axioms pushforwardEqIso
#print axioms pushforwardEqIso_hom
#print axioms pushforwardCompIso
#print axioms pullbackSquareIso
#print axioms pullbackComparison
#print axioms pullbackComparison_eq_iso_app
#print axioms pushforwardSquareMateIso
#print axioms pushforwardSquareIso
#print axioms pushforwardSquareIso_hom_eq
#print axioms pullbackCompIso_inv_mate
#print axioms pullbackCompIso_hom_mate
#print axioms mapEqIso_mate
#print axioms pushforwardSquareMateIso_eq
#print axioms mate
#print axioms transition
#print axioms transition_adjoint
#print axioms transition_proof_irrel
#print axioms adjoint_transition
#print axioms transition_comp
#print axioms adjoint_identity
#print axioms adjoint_composite
#print axioms transition_identity
#print axioms transition_composite

end TopCat.Sheaf.SquareTransition
