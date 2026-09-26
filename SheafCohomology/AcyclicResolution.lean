/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

public section

/-!
# Ext comparisons from acyclic resolutions

Covariant dimension shift for Ext and natural comparisons between Ext and
homology of a resolution by objects acyclic for the chosen functor.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The covariant dimension-shift equivalence attached to a short exact
sequence when the middle object has vanishing Ext in both adjacent degrees. -/
@[expose] noncomputable def covariantDimensionShift
    {S : ShortComplex C} (hS : S.ShortExact) (X : C) (n : ℕ)
    [Subsingleton (Ext X S.X₂ n)]
    [Subsingleton (Ext X S.X₂ (n + 1))] :
    Ext X S.X₃ n ≃+ Ext X S.X₁ (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.postcomp X rfl) <| by
    constructor
    · intro x y hxy
      have hzero :
          (x - y).comp hS.extClass rfl = 0 := by
        change (hS.extClass.postcomp X rfl) (x - y) = 0
        rw [map_sub, hxy, sub_self]
      obtain ⟨z, hz⟩ := covariant_sequence_exact₃ X hS (x - y) rfl hzero
      have hz₀ : z = 0 := Subsingleton.elim _ _
      rw [hz₀] at hz
      have hxy₀ : x - y = 0 := by simpa using hz.symm
      exact sub_eq_zero.mp hxy₀
    · intro y
      have hzero : y.comp (mk₀ S.f) (add_zero (n + 1)) = 0 :=
        Subsingleton.elim _ _
      obtain ⟨x, hx⟩ := covariant_sequence_exact₁ X hS y hzero rfl
      exact ⟨x, hx⟩

/-- The covariant connecting map defined by an extension class is natural in
maps of short exact sequences. -/
lemma covariantDimensionShift_naturality
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) (n : ℕ)
    (x : Ext X S₁.X₃ n) :
    (x.comp (mk₀ f.τ₃) (add_zero n)).comp h₂.extClass rfl =
      (x.comp h₁.extClass rfl).comp (mk₀ f.τ₁) (add_zero (n + 1)) := by
  rw [comp_assoc_of_second_deg_zero, comp_assoc_of_third_deg_zero]
  rw [h₁.extClass_naturality h₂ f]

/-- Degree-one Ext is the cokernel of the degree-zero map in a short exact
sequence when degree-one Ext of the middle object vanishes. -/
@[expose] noncomputable def covariantCokernelIso
    {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    [Subsingleton (Ext X S.X₂ 1)] :
    cokernel (AddCommGrpCat.ofHom
      ((mk₀ S.g).postcomp X (add_zero 0))) ≅ ↧(Ext X S.X₁ 1) := by
  let T : ShortComplex AddCommGrpCat.{w} :=
    ShortComplex.mk
      (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X (add_zero 0)))
      (AddCommGrpCat.ofHom (hS.extClass.postcomp X rfl))
      (by
        ext x
        change (x.comp (mk₀ S.g) (add_zero 0)).comp
          hS.extClass rfl = 0
        simp only [comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, comp_zero])
  have hT : T.Exact := covariant_sequence_exact₃' X hS 0 1 rfl
  have hTg : Epi T.g := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro y
    have hzero : y.comp (mk₀ S.f) (add_zero 1) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := covariant_sequence_exact₁ X hS y hzero rfl
    exact ⟨x, hx⟩
  let _ : Epi T.g := hTg
  exact colimit.isoColimitCocone
    ⟨CokernelCofork.ofπ T.g T.zero,
      ((ShortComplex.exact_and_epi_g_iff_g_is_cokernel T).1
        ⟨hT, inferInstance⟩).some⟩

@[reassoc (attr := simp)]
lemma cokernelπ_covariantCokernelIso_hom
    {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    [Subsingleton (Ext X S.X₂ 1)] :
    cokernel.π (AddCommGrpCat.ofHom
        ((mk₀ S.g).postcomp X (add_zero 0))) ≫
      (covariantCokernelIso hS X).hom =
        AddCommGrpCat.ofHom (hS.extClass.postcomp X rfl) := by
  dsimp [covariantCokernelIso]
  apply colimit.isoColimitCocone_ι_hom

/-- The map of the degree-zero cokernels induced by a map of short
complexes. -/
@[expose] noncomputable def covariantCokernelMap {S₁ S₂ : ShortComplex C}
    (f : S₁ ⟶ S₂) (X : C) :
    cokernel (AddCommGrpCat.ofHom
      ((mk₀ S₁.g).postcomp X (add_zero 0))) ⟶
        cokernel (AddCommGrpCat.ofHom
          ((mk₀ S₂.g).postcomp X (add_zero 0))) :=
  cokernel.map _ _
    (AddCommGrpCat.ofHom ((mk₀ f.τ₂).postcomp X (add_zero 0)))
    (AddCommGrpCat.ofHom ((mk₀ f.τ₃).postcomp X (add_zero 0))) (by
      ext x
      change (x.comp (mk₀ S₁.g) (add_zero 0)).comp
          (mk₀ f.τ₃) (add_zero 0) =
        (x.comp (mk₀ f.τ₂) (add_zero 0)).comp
          (mk₀ S₂.g) (add_zero 0)
      rw [comp_assoc_of_second_deg_zero, comp_assoc_of_second_deg_zero,
        mk₀_comp_mk₀, mk₀_comp_mk₀, f.comm₂₃])

@[reassoc]
lemma covariantCokernelIso_hom_naturality
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C)
    [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] :
    covariantCokernelMap f X ≫ (covariantCokernelIso h₂ X).hom =
      (covariantCokernelIso h₁ X).hom ≫
        AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X (add_zero 1)) := by
  apply (cancel_epi (cokernel.π (AddCommGrpCat.ofHom
    ((mk₀ S₁.g).postcomp X (add_zero 0))))).1
  dsimp only [covariantCokernelMap, cokernel.map]
  rw [cokernel.π_desc_assoc, Category.assoc,
    cokernelπ_covariantCokernelIso_hom,
    cokernelπ_covariantCokernelIso_hom_assoc]
  ext x
  exact covariantDimensionShift_naturality h₁ h₂ f X 0 x

@[reassoc]
lemma covariantCokernelIso_inv_naturality
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C)
    [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] :
    AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X (add_zero 1)) ≫
        (covariantCokernelIso h₂ X).inv =
      (covariantCokernelIso h₁ X).inv ≫ covariantCokernelMap f X := by
  rw [← cancel_epi (covariantCokernelIso h₁ X).hom,
    Iso.hom_inv_id_assoc,
    ← covariantCokernelIso_hom_naturality_assoc h₁ h₂ f X,
    Iso.hom_inv_id, Category.comp_id]

/-- A nonnegative resolution whose terms are acyclic for `Ext X -` in
positive degrees. -/
structure AcyclicResolution (X A : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ n, cocomplex.HasHomology n]
  ι : (CochainComplex.single₀ C).obj A ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance
  extAcyclic : ∀ n q, 0 < q → Subsingleton (Ext X (cocomplex.X n) q)

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

namespace AcyclicResolution

variable {X A : C} (R : AcyclicResolution X A)

variable {B : C} (R' : AcyclicResolution X B)

/-- A map of acyclic resolutions above a map of resolved objects. -/
structure Hom (f : A ⟶ B) where
  hom : R.cocomplex ⟶ R'.cocomplex
  ι_f_zero_comp_hom_f_zero :
    R.ι.f 0 ≫ hom.f 0 = ((CochainComplex.single₀ C).map f).f 0 ≫ R'.ι.f 0

namespace Hom

attribute [reassoc (attr := simp)] ι_f_zero_comp_hom_f_zero

set_option backward.isDefEq.respectTransparency false in
variable {R R'} in
@[reassoc (attr := simp)]
lemma ι_comp_hom {f : A ⟶ B} (φ : Hom R R' f) :
    R.ι ≫ φ.hom = (CochainComplex.single₀ C).map f ≫ R'.ι := by
  cat_disch

end Hom

variable {R'}

lemma cocomplex_exactAt_succ (n : ℕ) :
    R.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt R.ι (n + 1)
    (CochainComplex.exactAt_succ_single_obj _ _)]
  infer_instance

/-- The resolved object is canonically isomorphic to the degree-zero cycles
of an acyclic resolution. -/
@[expose] noncomputable def objectIsoCyclesZero : A ≅ R.cocomplex.cycles 0 :=
  (HomologicalComplex.singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt R.ι 0 ≪≫ R.cocomplex.isoHomologyπ₀.symm

@[reassoc]
lemma objectIsoCyclesZero_hom_naturality {f : A ⟶ B}
    (φ : Hom R R' f) :
    f ≫ R'.objectIsoCyclesZero.hom =
      R.objectIsoCyclesZero.hom ≫ HomologicalComplex.cyclesMap φ.hom 0 := by
  dsimp [objectIsoCyclesZero]
  simp only [isoOfQuasiIsoAt_hom]
  rw [Category.assoc, Category.assoc,
    ← CochainComplex.isoHomologyπ₀_inv_naturality,
    ← HomologicalComplex.homologyMap_comp_assoc, φ.ι_comp_hom,
    HomologicalComplex.homologyMap_comp_assoc,
    ← Category.assoc,
    ← HomologicalComplex.singleObjHomologySelfIso_inv_naturality]
  simp only [Category.assoc]

/-- Ext of the resolved object is transported to Ext of the degree-zero
cycles by the canonical augmentation isomorphism. -/
@[expose] noncomputable def extIsoCyclesZero (q : ℕ) :
    Ext X A q ≃+ Ext X (R.cocomplex.cycles 0) q :=
  ((extFunctorObj X q).mapIso R.objectIsoCyclesZero).addCommGroupIsoToAddEquiv

lemma extIsoCyclesZero_naturality {f : A ⟶ B} (φ : Hom R R' f)
    (q : ℕ) (x : Ext X A q) :
    R'.extIsoCyclesZero q (x.comp (mk₀ f) (add_zero q)) =
      (R.extIsoCyclesZero q x).comp
        (mk₀ (HomologicalComplex.cyclesMap φ.hom 0)) (add_zero q) := by
  change (x.comp (mk₀ f) (add_zero q)).comp
      (mk₀ R'.objectIsoCyclesZero.hom) (add_zero q) =
    (x.comp (mk₀ R.objectIsoCyclesZero.hom) (add_zero q)).comp
      (mk₀ (HomologicalComplex.cyclesMap φ.hom 0)) (add_zero q)
  rw [comp_assoc_of_second_deg_zero, comp_assoc_of_second_deg_zero,
    mk₀_comp_mk₀, mk₀_comp_mk₀,
    R.objectIsoCyclesZero_hom_naturality φ]

/-- The canonical sequence from degree-`n` cycles through the degree-`n`
term to degree-`n+1` cycles. -/
@[expose] noncomputable def cyclesShortComplex (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.cocomplex.iCycles n) (R.cocomplex.toCycles n (n + 1)) (by
    rw [← cancel_mono (R.cocomplex.iCycles (n + 1))]
    simp)

omit [HasExt C] in
@[reassoc]
lemma toCycles_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℕ)
    [K.HasHomology (n + 1)] [L.HasHomology (n + 1)] :
    f.f n ≫ L.toCycles n (n + 1) =
      K.toCycles n (n + 1) ≫ HomologicalComplex.cyclesMap f (n + 1) := by
  rw [← cancel_mono (L.iCycles (n + 1))]
  simp

/-- A cochain map induces a map of the canonical cycle short complexes. -/
@[expose] noncomputable def cyclesShortComplexMap
    {X' A' : C} {R' : AcyclicResolution X' A'}
    (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    R.cyclesShortComplex n ⟶ R'.cyclesShortComplex n where
  τ₁ := HomologicalComplex.cyclesMap f n
  τ₂ := f.f n
  τ₃ := HomologicalComplex.cyclesMap f (n + 1)
  comm₁₂ := by simp [cyclesShortComplex]
  comm₂₃ := by
    simpa [cyclesShortComplex] using toCycles_naturality f n

@[simp]
lemma cyclesShortComplexMap_id (n : ℕ) :
    R.cyclesShortComplexMap (𝟙 R.cocomplex) n = 𝟙 (R.cyclesShortComplex n) := by
  ext <;> dsimp [cyclesShortComplexMap, cyclesShortComplex] <;> simp

lemma cyclesShortComplexMap_comp
    {X' A' X'' A'' : C} {R' : AcyclicResolution X' A'}
    {R'' : AcyclicResolution X'' A''} (f : R.cocomplex ⟶ R'.cocomplex)
    (g : R'.cocomplex ⟶ R''.cocomplex) (n : ℕ) :
    R.cyclesShortComplexMap (f ≫ g) n =
      R.cyclesShortComplexMap f n ≫ R'.cyclesShortComplexMap g n := by
  ext <;> dsimp [cyclesShortComplexMap, cyclesShortComplex] <;>
    simp [HomologicalComplex.cyclesMap_comp]

lemma cyclesShortComplex_shortExact (n : ℕ) :
    (R.cyclesShortComplex n).ShortExact := by
  have hEpi : Epi (R.cocomplex.toCycles n (n + 1)) := by
    let S := R.cocomplex.sc' n (n + 1) (n + 2)
    have hExact : S.Exact :=
      (R.cocomplex.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).1
        (R.cocomplex_exactAt_succ n)
    let _ : Epi S.toCycles := hExact.epi_toCycles
    let e := R.cocomplex.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)
    let ae : Arrow.mk (R.cocomplex.toCycles n (n + 1)) ≅ Arrow.mk S.toCycles :=
      Arrow.isoMk (Iso.refl _) e (by
        dsimp [S, e]
        rw [R.cocomplex.toCycles_cyclesIsoSc'_hom]
        exact Category.id_comp _)
    exact ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ae).2 (by infer_instance)
  refine ShortComplex.ShortExact.mk' ?_ ?_ hEpi
  · dsimp [cyclesShortComplex]
    apply ShortComplex.exact_of_f_is_kernel
    exact Limits.isKernelOfComp
      (R.cocomplex.iCycles (n + 1)) (R.cocomplex.d n (n + 1))
        (R.cocomplex.cyclesIsKernel n (n + 1) (by simp))
          (by
            rw [← cancel_mono (R.cocomplex.iCycles (n + 1))]
            simp)
          (by simp)
  · change Mono (R.cocomplex.iCycles n)
    infer_instance

/-- One dimension shift along the canonical cycle short exact sequence. -/
@[expose] noncomputable def cyclesDimensionShift (n q : ℕ) (hq : 0 < q) :
    Ext X (R.cocomplex.cycles (n + 1)) q ≃+
      Ext X (R.cocomplex.cycles n) (q + 1) := by
  letI : Subsingleton (Ext X (R.cyclesShortComplex n).X₂ q) := by
    simpa [cyclesShortComplex] using R.extAcyclic n q hq
  letI : Subsingleton (Ext X (R.cyclesShortComplex n).X₂ (q + 1)) := by
    simpa [cyclesShortComplex] using R.extAcyclic n (q + 1) (by omega)
  exact covariantDimensionShift (R.cyclesShortComplex_shortExact n) X q

/-- Dimension shift along cycle short exact sequences is natural in a map of
resolution complexes. -/
lemma cyclesDimensionShift_naturality
    {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex)
    (n q : ℕ) (hq : 0 < q) (x : Ext X (R.cocomplex.cycles (n + 1)) q) :
    R'.cyclesDimensionShift n q hq
        (x.comp (mk₀ (HomologicalComplex.cyclesMap f (n + 1))) (add_zero q)) =
      (R.cyclesDimensionShift n q hq x).comp
        (mk₀ (HomologicalComplex.cyclesMap f n)) (add_zero (q + 1)) := by
  dsimp [cyclesDimensionShift, covariantDimensionShift]
  exact covariantDimensionShift_naturality
    (R.cyclesShortComplex_shortExact n) (R'.cyclesShortComplex_shortExact n)
      (R.cyclesShortComplexMap f n) X q x

private lemma cast_comp_degree_zero {Y Z : C} {p r : ℕ} (h : p = r)
    (x : Ext X Y p) (f : Y ⟶ Z) :
    AddEquiv.cast h (x.comp (mk₀ f) (add_zero p)) =
      (AddEquiv.cast h x).comp (mk₀ f) (add_zero r) := by
  subst r
  rfl

/-- Iterating the canonical dimension shifts moves Ext of degree-`n` cycles
back to Ext of the degree-zero cycles. -/
@[expose] noncomputable def cyclesDimensionShiftIterate :
    (n q : ℕ) → 0 < q → Ext X (R.cocomplex.cycles n) q ≃+
      Ext X (R.cocomplex.cycles 0) (n + q)
  | 0, q, _ => AddEquiv.cast (by omega)
  | n + 1, q, hq =>
      (R.cyclesDimensionShift n q hq).trans
        ((cyclesDimensionShiftIterate n (q + 1) (by omega)).trans
          (AddEquiv.cast (by omega)))

/-- The iterated dimension shift is natural in maps of resolution complexes. -/
lemma cyclesDimensionShiftIterate_naturality
    {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex)
    (n q : ℕ) (hq : 0 < q) (x : Ext X (R.cocomplex.cycles n) q) :
    R'.cyclesDimensionShiftIterate n q hq
        (x.comp (mk₀ (HomologicalComplex.cyclesMap f n)) (add_zero q)) =
      (R.cyclesDimensionShiftIterate n q hq x).comp
        (mk₀ (HomologicalComplex.cyclesMap f 0)) (add_zero (n + q)) := by
  induction n generalizing q with
  | zero =>
      dsimp [cyclesDimensionShiftIterate]
      apply cast_comp_degree_zero
  | succ n ih =>
      dsimp [cyclesDimensionShiftIterate]
      rw [R.cyclesDimensionShift_naturality R' f n q hq x]
      rw [ih (q + 1) (by omega)]
      apply cast_comp_degree_zero

/-- The inverse iterated dimension shift is natural in maps of resolution
complexes. -/
lemma cyclesDimensionShiftIterate_symm_naturality
    {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex)
    (n q : ℕ) (hq : 0 < q) (x : Ext X (R.cocomplex.cycles 0) (n + q)) :
    (R'.cyclesDimensionShiftIterate n q hq).symm
        (x.comp (mk₀ (HomologicalComplex.cyclesMap f 0)) (add_zero (n + q))) =
      ((R.cyclesDimensionShiftIterate n q hq).symm x).comp
        (mk₀ (HomologicalComplex.cyclesMap f n)) (add_zero q) := by
  apply (R'.cyclesDimensionShiftIterate n q hq).injective
  rw [AddEquiv.apply_symm_apply,
    R.cyclesDimensionShiftIterate_naturality R' f n q hq,
    AddEquiv.apply_symm_apply]

end AcyclicResolution

section SameUniverse

variable {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{v} D]

/-- Degree-zero Ext, as a functor in its second variable, is canonically the
preadditive coyoneda functor. -/
@[expose] noncomputable def extZeroCoyonedaIso (X : D) :
    extFunctorObj X 0 ≅ preadditiveCoyoneda.obj (Opposite.op X) :=
  NatIso.ofComponents (fun Y => Ext.addEquiv₀.toAddCommGrpIso) (by
    intro Y Z f
    ext x
    change Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) =
      Ext.addEquiv₀ x ≫ f
    apply (Ext.mk₀_bijective X Z).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀]
    exact congrArg (fun y : Ext X Y 0 =>
      y.comp (Ext.mk₀ f) (add_zero 0))
        (Ext.mk₀_addEquiv₀_apply (x : Ext X Y 0)).symm)

noncomputable instance (X : D) : PreservesFiniteLimits (extFunctorObj X 0) :=
  preservesFiniteLimits_of_natIso (extZeroCoyonedaIso X).symm

namespace AcyclicResolution

variable {X A : D} (R : AcyclicResolution X A)

/-- The degree-zero Ext functor applied termwise to an acyclic resolution. -/
noncomputable abbrev extZeroComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((extFunctorObj X 0).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex

/-- The additive coyoneda functor applied termwise to an acyclic resolution. -/
noncomputable abbrev homComplex : CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj R.cocomplex

/-- A map of resolutions induces a map on the degree-zero Ext complexes. -/
noncomputable abbrev extZeroComplexMap {B : D} (R' : AcyclicResolution X B)
    (f : R.cocomplex ⟶ R'.cocomplex) : R.extZeroComplex ⟶ R'.extZeroComplex :=
  ((extFunctorObj X 0).mapHomologicalComplex (ComplexShape.up ℕ)).map f

/-- A map of resolutions induces a map on the additive coyoneda complexes. -/
noncomputable abbrev homComplexMap {B : D} (R' : AcyclicResolution X B)
    (f : R.cocomplex ⟶ R'.cocomplex) : R.homComplex ⟶ R'.homComplex :=
  ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map f

/-- The termwise degree-zero Ext complex is canonically isomorphic to the
additive coyoneda complex. -/
@[expose] noncomputable def extZeroComplexIsoHomComplex :
    R.extZeroComplex ≅ R.homComplex :=
  (NatIso.mapHomologicalComplex (extZeroCoyonedaIso X)
    (ComplexShape.up ℕ)).app R.cocomplex

@[reassoc]
lemma extZeroComplexIsoHomComplex_hom_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) :
    R.extZeroComplexMap R' f ≫ R'.extZeroComplexIsoHomComplex.hom =
      R.extZeroComplexIsoHomComplex.hom ≫ R.homComplexMap R' f :=
  (NatIso.mapHomologicalComplex (extZeroCoyonedaIso X)
    (ComplexShape.up ℕ)).hom.naturality f

/-- The induced canonical isomorphism on homology. -/
@[expose] noncomputable def extZeroHomologyIsoHomology (n : ℕ) :
    R.extZeroComplex.homology n ≅ R.homComplex.homology n :=
  HomologicalComplex.homologyMapIso R.extZeroComplexIsoHomComplex n

@[reassoc]
lemma extZeroHomologyIsoHomology_hom_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n ≫
        (R'.extZeroHomologyIsoHomology n).hom =
      (R.extZeroHomologyIsoHomology n).hom ≫
        HomologicalComplex.homologyMap (R.homComplexMap R' f) n := by
  dsimp [extZeroHomologyIsoHomology,
    HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    R.extZeroComplexIsoHomComplex_hom_naturality R' f,
    HomologicalComplex.homologyMap_comp]

lemma extZeroHomologyIsoHomology_hom_naturality_apply {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    (x : ↑(R.extZeroComplex.homology n)) :
    (R'.extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n x) =
      HomologicalComplex.homologyMap (R.homComplexMap R' f) n
        ((R.extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv x) := by
  have h := congrArg (fun g ↦ g x)
    (R.extZeroHomologyIsoHomology_hom_naturality R' f n)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

lemma extZeroHomology_eqToIso_naturality_apply {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex)
    {m n : ℕ} (h : m = n) (x : ↑(R.extZeroComplex.homology m)) :
    (eqToIso (congrArg (fun i ↦ R'.extZeroComplex.homology i) h)).addCommGroupIsoToAddEquiv
        (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) m x) =
      HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n
        ((eqToIso (congrArg (fun i ↦ R.extZeroComplex.homology i) h)).addCommGroupIsoToAddEquiv
          x) := by
  subst n
  rfl

/-- Degree-zero Ext preserves the cycle kernel of a resolution complex. -/
@[expose] noncomputable def extZeroCyclesIso (n : ℕ) :
    R.extZeroComplex.cycles n ≅
      (extFunctorObj X 0).obj (R.cocomplex.cycles n) :=
  ((R.extZeroComplex.sc n).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (R.cocomplex.sc n).cyclesIsKernel
      (extFunctorObj X 0))).symm

@[reassoc (attr := simp)]
lemma extZeroCyclesIso_hom_map_iCycles (n : ℕ) :
    (R.extZeroCyclesIso n).hom ≫
        (extFunctorObj X 0).map (R.cocomplex.iCycles n) =
      R.extZeroComplex.iCycles n := by
  dsimp [extZeroCyclesIso]
  apply ShortComplex.isoCyclesOfIsLimit_inv_ι

@[reassoc]
lemma extZeroCyclesIso_hom_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n ≫
        (R'.extZeroCyclesIso n).hom =
      (R.extZeroCyclesIso n).hom ≫
        (extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n) := by
  rw [← cancel_mono ((extFunctorObj X 0).map (R'.cocomplex.iCycles n))]
  simp only [Category.assoc, extZeroCyclesIso_hom_map_iCycles,
    HomologicalComplex.cyclesMap_i, ← Functor.map_comp]
  rw [Functor.map_comp, ← Category.assoc,
    R.extZeroCyclesIso_hom_map_iCycles]
  rfl

@[reassoc]
lemma extZeroCyclesIso_inv_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    (extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n) ≫
        (R'.extZeroCyclesIso n).inv =
      (R.extZeroCyclesIso n).inv ≫
        HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n := by
  rw [← cancel_epi (R.extZeroCyclesIso n).hom, Iso.hom_inv_id_assoc,
    ← R.extZeroCyclesIso_hom_naturality_assoc R' f n,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma extZero_toCycles_mapCyclesIso_hom (n : ℕ) :
    R.extZeroComplex.toCycles n (n + 1) ≫
        (R.extZeroCyclesIso (n + 1)).hom =
      (extFunctorObj X 0).map (R.cocomplex.toCycles n (n + 1)) := by
  rw [← cancel_mono ((extFunctorObj X 0).map (R.cocomplex.iCycles (n + 1)))]
  rw [Category.assoc, extZeroCyclesIso_hom_map_iCycles,
    HomologicalComplex.toCycles_i, ← Functor.map_comp,
    HomologicalComplex.toCycles_i]
  rfl

/-- The dimension-shift cokernel is canonically the degree-one Ext group of
the cycles in the same degree. -/
@[expose] noncomputable def cyclesCokernelIso (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] :
    cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) ≅
        ↧(Ext X (R.cocomplex.cycles n) 1) :=
  covariantCokernelIso (R.cyclesShortComplex_shortExact n) X

/-- The cokernel arising in the degree-one dimension shift is canonically the
homology of the degree-zero Ext complex in the next degree. -/
@[expose] noncomputable def extZeroCokernelIsoHomology (n : ℕ) :
    cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) ≅
        R.extZeroComplex.homology (n + 1) := by
  let e := R.extZeroCyclesIso (n + 1)
  let π := e.inv ≫ R.extZeroComplex.homologyπ (n + 1)
  have w : (extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1)) ≫ π = 0 := by
    dsimp [π, e]
    rw [← R.extZero_toCycles_mapCyclesIso_hom n]
    simp
  let c : CokernelCofork ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) := CokernelCofork.ofπ π w
  haveI : Epi π := by dsimp [π]; infer_instance
  have hc : IsColimit c := CokernelCofork.IsColimit.ofπ' π w (fun k hk => by
    let k' := e.hom ≫ k
    have hk' : R.extZeroComplex.toCycles n (n + 1) ≫ k' = 0 := by
      dsimp [k', e]
      rw [R.extZero_toCycles_mapCyclesIso_hom_assoc n, hk]
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
      (R.extZeroComplex.homologyIsCokernel n (n + 1) (by simp)) k' hk'
    refine ⟨l, ?_⟩
    change R.extZeroComplex.homologyπ (n + 1) ≫ l = k' at hl
    dsimp [π]
    rw [Category.assoc, hl]
    dsimp [k', e]
    rw [Iso.inv_hom_id_assoc])
  exact colimit.isoColimitCocone ⟨c, hc⟩

@[reassoc (attr := simp)]
lemma cokernelπ_extZeroCokernelIsoHomology_hom (n : ℕ) :
    cokernel.π ((extFunctorObj X 0).map
        (R.cocomplex.toCycles n (n + 1))) ≫
      (R.extZeroCokernelIsoHomology n).hom =
        (R.extZeroCyclesIso (n + 1)).inv ≫
          R.extZeroComplex.homologyπ (n + 1) := by
  dsimp [extZeroCokernelIsoHomology]
  apply colimit.isoColimitCocone_ι_hom

/-- The map of dimension-shift cokernels induced by a map of resolution
complexes. -/
@[expose] noncomputable def extZeroCokernelMap {B : D} (R' : AcyclicResolution X B)
    (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) ⟶
        cokernel ((extFunctorObj X 0).map
          (R'.cocomplex.toCycles n (n + 1))) :=
  cokernel.map _ _ ((extFunctorObj X 0).map (f.f n))
    ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f (n + 1))) (by
      rw [← Functor.map_comp, ← Functor.map_comp,
        toCycles_naturality f n])

@[reassoc]
lemma cyclesCokernelIso_hom_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] :
    R.extZeroCokernelMap R' f n ≫
        (R'.cyclesCokernelIso n).hom =
      (R.cyclesCokernelIso n).hom ≫
        AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X
          (add_zero 1)) := by
  change covariantCokernelMap (R.cyclesShortComplexMap f n) X ≫
      (covariantCokernelIso (R'.cyclesShortComplex_shortExact n) X).hom = _
  exact covariantCokernelIso_hom_naturality
    (R.cyclesShortComplex_shortExact n) (R'.cyclesShortComplex_shortExact n)
      (R.cyclesShortComplexMap f n) X

@[reassoc]
lemma cyclesCokernelIso_inv_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] :
    AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X
        (add_zero 1)) ≫
        (R'.cyclesCokernelIso n).inv =
      (R.cyclesCokernelIso n).inv ≫ R.extZeroCokernelMap R' f n := by
  rw [← cancel_epi (R.cyclesCokernelIso n).hom,
    Iso.hom_inv_id_assoc,
    ← R.cyclesCokernelIso_hom_naturality_assoc R' f n,
    Iso.hom_inv_id, Category.comp_id]

lemma cyclesCokernelIso_inv_naturality_apply {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)]
    (x : Ext X (R.cocomplex.cycles n) 1) :
    (R'.cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm
        (x.comp (mk₀ (HomologicalComplex.cyclesMap f n)) (add_zero 1)) =
      R.extZeroCokernelMap R' f n
        ((R.cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm x) := by
  have h := congrArg (fun g ↦ g x)
    (R.cyclesCokernelIso_inv_naturality R' f n)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

@[reassoc]
lemma extZeroCokernelIsoHomology_hom_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    R.extZeroCokernelMap R' f n ≫
        (R'.extZeroCokernelIsoHomology n).hom =
      (R.extZeroCokernelIsoHomology n).hom ≫
        HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) (n + 1) := by
  rw [← cancel_epi (cokernel.π ((extFunctorObj X 0).map
    (R.cocomplex.toCycles n (n + 1))))]
  dsimp [extZeroCokernelMap]
  rw [cokernel.π_desc_assoc, Category.assoc,
    R'.cokernelπ_extZeroCokernelIsoHomology_hom,
    R.extZeroCyclesIso_inv_naturality_assoc R' f (n + 1),
    ← HomologicalComplex.homologyπ_naturality,
    R.cokernelπ_extZeroCokernelIsoHomology_hom_assoc]

lemma extZeroCokernelIsoHomology_hom_naturality_apply {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    (x : ↑(cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))))) :
    (R'.extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv
        (R.extZeroCokernelMap R' f n x) =
      HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) (n + 1)
        ((R.extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv x) := by
  have h := congrArg (fun g ↦ g x)
    (R.extZeroCokernelIsoHomology_hom_naturality R' f n)
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply] at h
  exact h

/-- Positive-degree Ext of the resolved object is canonically the homology of
the additive coyoneda complex of any acyclic resolution. -/
@[expose] noncomputable def extPositiveIsoHomology (q : ℕ) (hq : 0 < q) :
    Ext X A q ≃+ ↑(R.homComplex.homology q) := by
  letI : Subsingleton (Ext X (R.cyclesShortComplex (q - 1)).X₂ 1) := by
    simpa [cyclesShortComplex] using R.extAcyclic (q - 1) 1 (by omega)
  exact (R.extIsoCyclesZero q).trans <|
    (AddEquiv.cast (by omega)).trans <|
      (R.cyclesDimensionShiftIterate (q - 1) 1 (by omega)).symm.trans <|
        (R.cyclesCokernelIso (q - 1)).addCommGroupIsoToAddEquiv.symm.trans <|
          (R.extZeroCokernelIsoHomology (q - 1)).addCommGroupIsoToAddEquiv.trans <|
            (eqToIso (congrArg (fun n => R.extZeroComplex.homology n)
              (by omega))).addCommGroupIsoToAddEquiv.trans <|
              (R.extZeroHomologyIsoHomology q).addCommGroupIsoToAddEquiv

/-- The positive-degree Ext comparison is natural in maps of acyclic
resolutions. -/
lemma extPositiveIsoHomology_naturality {B : D} {f : A ⟶ B}
    (R' : AcyclicResolution X B) (φ : Hom R R' f) (q : ℕ) (hq : 0 < q)
    (x : Ext X A q) :
    R'.extPositiveIsoHomology q hq (x.comp (mk₀ f) (add_zero q)) =
      HomologicalComplex.homologyMap (R.homComplexMap R' φ.hom) q
        (R.extPositiveIsoHomology q hq x) := by
  let _ : Subsingleton (Ext X (R.cyclesShortComplex (q - 1)).X₂ 1) := by
    simpa [cyclesShortComplex] using R.extAcyclic (q - 1) 1 (by omega)
  let _ : Subsingleton (Ext X (R'.cyclesShortComplex (q - 1)).X₂ 1) := by
    simpa [cyclesShortComplex] using R'.extAcyclic (q - 1) 1 (by omega)
  dsimp [extPositiveIsoHomology]
  rw [R.extIsoCyclesZero_naturality φ q x]
  rw [cast_comp_degree_zero]
  rw [R.cyclesDimensionShiftIterate_symm_naturality R' φ.hom
    (q - 1) 1 (by omega)]
  rw [R.cyclesCokernelIso_inv_naturality_apply R' φ.hom (q - 1)]
  rw [R.extZeroCokernelIsoHomology_hom_naturality_apply R' φ.hom
    (q - 1)]
  rw [R.extZeroHomology_eqToIso_naturality_apply R' φ.hom (by omega)]
  rw [R.extZeroHomologyIsoHomology_hom_naturality_apply R' φ.hom q]

end AcyclicResolution

end SameUniverse

end CategoryTheory.Abelian.Ext
