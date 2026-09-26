/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.FlasqueResolution

public section

/-!
# The functorial flasque resolution as an acyclic resolution

This file packages the stalk-skyscraper flasque resolution as an
`Abelian.Ext.AcyclicResolution` on compact prespectral quasi-separated spaces.
It also records the induced map of acyclic resolutions above a map of sheaves.

The construction has the same small-universe boundary as the current
functorial flasque resolution and quasi-flasque acyclicity theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

/-- The functorial flasque resolution, packaged as a resolution acyclic for
the Ext functor defining sheaf cohomology. -/
@[expose] noncomputable def flasqueAcyclicResolution
    [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat)]
    (F : Sheaf AddCommGrpCat X) :
    Abelian.Ext.AcyclicResolution
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        ↧(ULift ℤ)) F where
  cocomplex := flasqueResolution F
  ι := toFlasqueResolution F
  quasiIso := toFlasqueResolution_quasiIso F
  extAcyclic n q hq := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact IsQuasiFlasque.subsingleton_H_succ q ((flasqueResolution F).X n)

@[simp]
lemma flasqueResolutionNat_map_f_zero
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    ((flasqueResolutionNat (X := X)).asFunctor.map f).f 0 =
      (flasqueEnvelopeFunctor (X := X)).map f := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of the flasque resolution gives a map of its packaged
acyclic resolutions above every map of sheaves. -/
@[expose] noncomputable def flasqueAcyclicResolutionHom
    [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat)]
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    Abelian.Ext.AcyclicResolution.Hom
      (flasqueAcyclicResolution F) (flasqueAcyclicResolution G) f where
  hom := (flasqueResolutionNat (X := X)).asFunctor.map f
  ι_f_zero_comp_hom_f_zero := by
    dsimp only [flasqueAcyclicResolution]
    simpa only [CochainComplex.single₀_map_f_zero,
      toFlasqueResolution_f_zero, flasqueResolutionNat_map_f_zero,
      Functor.id_obj, Functor.id_map] using
        ((toFlasqueEnvelope (X := X)).naturality f).symm

end TopCat.Sheaf
