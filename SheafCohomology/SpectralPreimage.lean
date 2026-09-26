/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.Prespectral

public section

set_option warningAsError true

/-!
# Coherent inverse images of compact opens

This file packages the exact topological classes inherited by the inverse
image of a compact open under a spectral map.
-/

open Set TopologicalSpace Topology

universe uX uY

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X : Type uX} {Y : Type uY}
variable [TopologicalSpace X] [TopologicalSpace Y]

abbrev preimageOpenType (f : X → Y) (V : Opens Y) :=
  {x : X // f x ∈ V}

theorem preimagePrespectralSpace [PrespectralSpace X]
    {f : X → Y} (hf : IsSpectralMap f) (V : Opens Y) :
    PrespectralSpace (preimageOpenType f V) :=
  (V.2.preimage hf.continuous).isOpenEmbedding_subtypeVal.prespectralSpace

theorem preimageCompactSpace {f : X → Y} (hf : IsSpectralMap f)
    (V : Opens Y) (hV : IsCompact (V : Set Y)) :
    CompactSpace (preimageOpenType f V) :=
  isCompact_iff_compactSpace.mp (hV.preimage_of_isOpen hf V.2)

theorem preimageQuasiSeparatedSpace [QuasiSeparatedSpace X]
    {f : X → Y} (hf : IsSpectralMap f) (V : Opens Y) :
    QuasiSeparatedSpace (preimageOpenType f V) :=
  (V.2.preimage hf.continuous).isOpenEmbedding_subtypeVal.quasiSeparatedSpace

/-- The prespectral, compact, and quasi-separated classes hold on a
compact-open preimage. The `Nonempty` wrappers keep this theorem independent of
global typeclass installation. -/
theorem preimage_coherent_classes [PrespectralSpace X]
    [QuasiSeparatedSpace X] {f : X → Y} (hf : IsSpectralMap f)
    (V : Opens Y) (hV : IsCompact (V : Set Y)) :
    Nonempty (PrespectralSpace (preimageOpenType f V)) ∧
      Nonempty (CompactSpace (preimageOpenType f V)) ∧
      Nonempty (QuasiSeparatedSpace (preimageOpenType f V)) :=
  ⟨⟨preimagePrespectralSpace hf V⟩,
    ⟨preimageCompactSpace hf V hV⟩,
    ⟨preimageQuasiSeparatedSpace hf V⟩⟩

#print axioms preimagePrespectralSpace
#print axioms preimageCompactSpace
#print axioms preimageQuasiSeparatedSpace
#print axioms preimage_coherent_classes

end SheafCohomology.HigherDirectImageFilteredColimit
