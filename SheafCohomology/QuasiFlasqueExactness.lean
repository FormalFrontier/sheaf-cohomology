/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.QuasiFlasque
public import Mathlib.Algebra.Category.Grp.Zero

public section

/-!
# Exactness for quasi-flasque sheaves

This file implements the finite compact-open correction argument.  It proves
surjectivity on compact-open sections for a short exact sequence with
quasi-flasque kernel, the global-sections specialization, and closure of
quasi-flasque sheaves under such quotients.

The proof is intentionally same-universe for now: the pinned mathlib lemmas
`Sheaf.sections_exact_of_left_exact` and
`TopCat.Sheaf.isLocallySurjective_iff_epi` specialize both
`X : TopCat.{u}` and `AddCommGrpCat.{u}` to one universe.  Generalizing those
bridges, or replacing them with independently universe-polymorphic arguments,
is an explicit same-universe limitation of the current API.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat Presheaf

universe u

namespace TopCat.Sheaf.IsQuasiFlasque

variable {X : TopCat.{u}} [QuasiSeparatedSpace X]

/-- The two-open correction step in the quasi-flasque exactness argument. -/
theorem exists_lift_sup
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁]
    (T U V : Opens X) (hUT : U ≤ T) (hVT : V ≤ T)
    (hUc : IsCompact (U : Set X)) (hVc : IsCompact (V : Set X))
    (s₃ : S.X₃.obj.obj (op T))
    (sU : S.X₂.obj.obj (op U))
    (hsU : S.g.hom.app (op U) sU = restrictOpen s₃ U hUT)
    (sV : S.X₂.obj.obj (op V))
    (hsV : S.g.hom.app (op V) sV = restrictOpen s₃ V hVT) :
    ∃ s : S.X₂.obj.obj (op (U ⊔ V)),
      S.g.hom.app (op (U ⊔ V)) s = restrictOpen s₃ (U ⊔ V) (sup_le hUT hVT) := by
  let W := U ⊓ V
  let d : S.X₂.obj.obj (op W) :=
    restrictOpen sU W inf_le_left - restrictOpen sV W inf_le_right
  have hd : S.g.hom.app (op W) d = 0 := by
    simp [d, W, map_restrict, hsU, hsV, restrict_restrict]
  obtain ⟨e, he⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 d hd
  have hWc : IsCompact (W : Set X) :=
    hUc.inter_of_isOpen hVc U.2 V.2
  obtain ⟨c, hc⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((restriction W).app S.X₁)).mp
      (epi_restriction (F := S.X₁) W hWc) e
  change restrictOpen c W le_top = e at hc
  let f : Fin 2 → Opens X := ![U, V]
  let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
    | 0 => sU
    | 1 => sV + S.f.hom.app (op V) (restrictOpen c V le_top)
  have h01 :
      restrictOpen (sf 0) (U ⊓ V) inf_le_left =
        restrictOpen (sf 1) (U ⊓ V) inf_le_right := by
    dsimp [sf, f]
    rw [restrict_sum, ← map_restrict, restrict_restrict]
    change restrictOpen c W le_top = e at hc
    rw [hc, he]
    dsimp [d, W]
    abel
  have h10 :
      restrictOpen (sf 1) (V ⊓ U) inf_le_left =
        restrictOpen (sf 0) (V ⊓ U) inf_le_right := by
    calc
      restrictOpen (sf 1) (V ⊓ U) inf_le_left =
          restrictOpen (restrictOpen (sf 1) (U ⊓ V) inf_le_right)
            (V ⊓ U) (le_of_eq (inf_comm V U)) :=
        (restrict_restrict (le_of_eq (inf_comm V U)) inf_le_right (sf 1)).symm
      _ = restrictOpen (restrictOpen (sf 0) (U ⊓ V) inf_le_left)
            (V ⊓ U) (le_of_eq (inf_comm V U)) :=
        congrArg
          (fun s ↦ restrictOpen s (V ⊓ U) (le_of_eq (inf_comm V U))) h01.symm
      _ = restrictOpen (sf 0) (V ⊓ U) inf_le_right :=
        restrict_restrict (le_of_eq (inf_comm V U)) inf_le_left (sf 0)
  have hcompat : IsCompatible S.X₂.obj f sf := by
    simp only [IsCompatible, Fin.forall_fin_two]
    exact ⟨⟨rfl, h01⟩, h10, rfl⟩
  let inc : (i : Fin 2) → f i ⟶ U ⊔ V := fun i => homOfLE (by
    fin_cases i <;> simp [f])
  have hcover : U ⊔ V ≤ iSup f := by
    apply sup_le
    · simpa [f] using le_iSup f (0 : Fin 2)
    · simpa [f] using le_iSup f (1 : Fin 2)
  obtain ⟨s, hs, _⟩ :=
    S.X₂.existsUnique_gluing' f (U ⊔ V) inc hcover sf hcompat
  refine ⟨s, ?_⟩
  apply S.X₃.eq_of_locally_eq' f (U ⊔ V) inc hcover
  intro i
  rw [← NatTrans.naturality_apply, hs]
  fin_cases i
  · dsimp [sf, f]
    change S.g.hom.app (op U) sU =
      restrictOpen (restrictOpen s₃ (U ⊔ V) (sup_le hUT hVT)) U (inc 0).le
    rw [hsU]
    exact (restrict_restrict (inc 0).le (sup_le hUT hVT) s₃).symm
  · dsimp [sf, f]
    have hzero : S.f.hom.app (op V) ≫ S.g.hom.app (op V) = 0 := by
      rw [← NatTrans.comp_app]
      change (S.f ≫ S.g).hom.app (op V) = 0
      rw [S.zero]
      rfl
    change S.g.hom.app (op V)
        (sV + S.f.hom.app (op V) (restrictOpen c V le_top)) =
      restrictOpen (restrictOpen s₃ (U ⊔ V) (sup_le hUT hVT)) V (inc 1).le
    calc
      S.g.hom.app (op V)
          (sV + S.f.hom.app (op V) (restrictOpen c V le_top)) =
        S.g.hom.app (op V) sV +
          S.g.hom.app (op V)
            (S.f.hom.app (op V) (restrictOpen c V le_top)) := map_add _ _ _
      _ = S.g.hom.app (op V) sV +
          (S.f.hom.app (op V) ≫ S.g.hom.app (op V))
            (restrictOpen c V le_top) := rfl
      _ = S.g.hom.app (op V) sV := by rw [hzero]; simp
      _ = restrictOpen s₃ V hVT := hsV
      _ = restrictOpen (restrictOpen s₃ (U ⊔ V) (sup_le hUT hVT)) V (inc 1).le :=
        (restrict_restrict (inc 1).le (sup_le hUT hVT) s₃).symm

omit [QuasiSeparatedSpace X] in
private theorem isCompact_finset_sup {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (U : ι → Opens X) (hU : ∀ i ∈ A, IsCompact (U i : Set X)) :
    IsCompact ((A.sup U : Opens X) : Set X) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sup_insert]
      rw [Opens.coe_sup]
      exact (hU a (by simp)).union (ih fun i hi ↦ hU i (by simp [hi]))

/-- A compatible family of local lifts on finitely many compact opens can be
corrected and glued to a lift on their union. -/
theorem exists_lift_finset {ι : Type*} [DecidableEq ι]
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁]
    (T : Opens X) (A : Finset ι) (U : ι → Opens X)
    (hUT : ∀ i ∈ A, U i ≤ T)
    (hUc : ∀ i ∈ A, IsCompact (U i : Set X))
    (s₃ : S.X₃.obj.obj (op T))
    (sU : (i : ι) → S.X₂.obj.obj (op (U i)))
    (hsU : ∀ i (hi : i ∈ A),
      S.g.hom.app (op (U i)) (sU i) = restrictOpen s₃ (U i) (hUT i hi)) :
    ∃ s : S.X₂.obj.obj (op (A.sup U)),
      S.g.hom.app (op (A.sup U)) s =
        restrictOpen s₃ (A.sup U) (Finset.sup_le fun i hi ↦ hUT i hi) := by
  classical
  revert hUT hUc hsU
  induction A using Finset.induction_on with
  | empty =>
      intro hUT hUc hsU
      refine ⟨0, ?_⟩
      have hzero : IsZero (S.X₃.obj.obj (op ((∅ : Finset ι).sup U))) := by
        simpa using S.X₃.isTerminalOfEmpty.isZero
      exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hzero) _ _
  | @insert a A ha ih =>
      intro hUT hUc hsU
      have hAT : A.sup U ≤ T :=
        Finset.sup_le fun i hi ↦ hUT i (Finset.mem_insert_of_mem hi)
      have haT : U a ≤ T := hUT a (Finset.mem_insert_self a A)
      obtain ⟨sA, hsA⟩ := ih
        (fun i hi ↦ hUT i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hUc i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hsU i (Finset.mem_insert_of_mem hi))
      obtain ⟨s, hs⟩ := exists_lift_sup hS T (U a) (A.sup U)
        haT hAT (hUc a (Finset.mem_insert_self a A))
        (isCompact_finset_sup A U
          (fun i hi ↦ hUc i (Finset.mem_insert_of_mem hi)))
        s₃ (sU a) (hsU a (Finset.mem_insert_self a A)) sA hsA
      have hsup : U a ⊔ A.sup U = (insert a A).sup U := by
        rw [Finset.sup_insert]
      let e := (eqToHom hsup.symm).op
      refine ⟨S.X₂.obj.map e s, ?_⟩
      calc
        S.g.hom.app (op ((insert a A).sup U)) (S.X₂.obj.map e s) =
            S.X₃.obj.map e (S.g.hom.app (op (U a ⊔ A.sup U)) s) := by
          rw [← NatTrans.naturality_apply]
        _ = S.X₃.obj.map e
            (restrictOpen s₃ (U a ⊔ A.sup U) (sup_le haT hAT)) :=
          congrArg _ hs
        _ = restrictOpen s₃ ((insert a A).sup U)
            (Finset.sup_le fun i hi ↦ hUT i hi) := by
          change S.X₃.obj.map e
              (S.X₃.obj.map (homOfLE (sup_le haT hAT)).op s₃) =
            S.X₃.obj.map
              (homOfLE (Finset.sup_le fun i hi ↦ hUT i hi)).op s₃
          rw [← Functor.map_comp_apply]
          exact congrArg (fun k ↦ S.X₃.obj.map k s₃) (Subsingleton.elim _ _)

/-- In a prespectral quasi-separated space, a short exact sequence whose
kernel is quasi-flasque is surjective on every compact open. -/
theorem epi_app_of_shortExact
    [PrespectralSpace X]
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁] (T : Opens X) (hTc : IsCompact (T : Set X)) :
    Epi (S.g.hom.app (op T)) := by
  classical
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s₃ ↦ ?_)
  have hlocally : Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  have hlocal : ∀ x : T,
      ∃ V : Opens X, ∃ hVT : V ≤ T,
        IsCompact (V : Set X) ∧ (x : X) ∈ V ∧
        ∃ sV : S.X₂.obj.obj (op V),
          S.g.hom.app (op V) sV = restrictOpen s₃ V hVT := by
    intro x
    obtain ⟨W, hWT, ⟨sW, hsW⟩, hxW⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hlocally T s₃ x x.property
    obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVW⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxW W.2
    let V' : Opens X := ⟨V, hVo⟩
    have hV'W : V' ≤ W := hVW
    have hV'T : V' ≤ T := le_trans hV'W hWT
    refine ⟨V', hV'T, hVc, hxV, restrictOpen sW V' hV'W, ?_⟩
    simp [map_restrict, hsW, restrict_restrict]
  choose V hVT hVc hxV sV hsV using hlocal
  obtain ⟨A, hcover⟩ := hTc.elim_finite_subcover
    (fun x : T ↦ (V x : Set X)) (fun x ↦ (V x).2) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  have hsup : A.sup V = T := by
    apply le_antisymm
    · exact Finset.sup_le fun i _ ↦ hVT i
    · intro x hx
      have hx' := hcover hx
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨i, hi, hxi⟩ := hx'
      exact Finset.le_sup (f := V) hi hxi
  obtain ⟨s, hs⟩ := exists_lift_finset hS T A V
    (fun i _ ↦ hVT i) (fun i _ ↦ hVc i) s₃ sV (fun i _ ↦ hsV i)
  let e := (eqToHom hsup.symm).op
  refine ⟨S.X₂.obj.map e s, ?_⟩
  calc
    S.g.hom.app (op T) (S.X₂.obj.map e s) =
        S.X₃.obj.map e (S.g.hom.app (op (A.sup V)) s) := by
      rw [← NatTrans.naturality_apply]
    _ = S.X₃.obj.map e
        (restrictOpen s₃ (A.sup V) (Finset.sup_le fun i hi ↦ hVT i)) :=
      congrArg _ hs
    _ = s₃ := by
      change S.X₃.obj.map e
          (S.X₃.obj.map
            (homOfLE (Finset.sup_le fun i hi ↦ hVT i)).op s₃) = s₃
      rw [← Functor.map_comp_apply]
      have he : (homOfLE (Finset.sup_le fun i hi ↦ hVT i)).op ≫ e = 𝟙 (op T) :=
        Subsingleton.elim _ _
      rw [he, S.X₃.obj.map_id]
      rfl

/-- On a compact prespectral quasi-separated space, a short exact sequence
whose kernel is quasi-flasque is surjective on global sections. -/
theorem epi_of_shortExact
    [CompactSpace X] [PrespectralSpace X]
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁] : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
  epi_app_of_shortExact hS ⊤ isCompact_univ

/-- In a prespectral quasi-separated space, a quotient of quasi-flasque
abelian sheaves in a short exact sequence is quasi-flasque. -/
theorem of_shortExact_of_isQuasiFlasque₁₂
    [PrespectralSpace X]
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsQuasiFlasque S.X₁] [IsQuasiFlasque S.X₂] : IsQuasiFlasque S.X₃ where
  epi_restriction U hU := by
    let i := (homOfLE le_top : U ⟶ (⊤ : Opens X)).op
    have hleft : Epi (S.X₂.obj.map i ≫ S.g.hom.app (op U)) := by
      let _ : Epi (S.X₂.obj.map i) :=
        IsQuasiFlasque.epi_restriction (F := S.X₂) U hU
      let _ : Epi (S.g.hom.app (op U)) := epi_app_of_shortExact hS U hU
      infer_instance
    have hright : Epi
        (S.g.hom.app (op (⊤ : Opens X)) ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact hleft
    exact CategoryTheory.epi_of_epi
      (S.g.hom.app (op (⊤ : Opens X))) (S.X₃.obj.map i)

end TopCat.Sheaf.IsQuasiFlasque
