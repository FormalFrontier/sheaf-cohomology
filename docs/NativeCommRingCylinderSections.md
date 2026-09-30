<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# Commutative-ring sections of a native open cylinder

Import `SheafCohomology.NativeCommRingCylinderSections` to work
directly with ring-valued sections on the inverse-image open in an **original**
native cone. This module uses this library's
[ring comparison](../SheafCohomology/NativeCommRingGlobalSections.lean) and
[native cylinder](../SheafCohomology/NativeCylinderLimit.lean).
No source-repository files are needed to use it.

For varying stage opens, the
[generic cylinder open-naturality guide](NativeCylinderOpenNaturality.md)
identifies this same ring comparison with the generic arbitrary-original-cone
arrow and derives its restriction square from the actual restricted-stage
transformation. That arrow law requires neither a limiting cone nor spectral
or compact-open hypotheses; the pointwise `IsIso` result below retains its
separate assumptions.

Let `ι` be a directed preorder, `S : ιᵒᵖ ⥤ SheafedSpace CommRingCat`
an inverse diagram, `i0 : ι`, `m : Cone S` an *arbitrary* original cone,
and `U0 : Opens (S.obj (op i0))`. Set `V := coneOpen S i0 m U0` and
`Ui := stageOpen S i0 U0 i` for `i : Set.Ici i0`. The literal tail
`restricted S i0 U0` consists of the restrictions of the original stages to
their named opens `Ui`; `restrictedCone S i0 m U0` restricts the given cone
point to `V`.

In `AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`:

- `nativeCommRingCylinderSectionsComparison S i0 m U0` is a ring morphism
  `colimit ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) ⟶
  m.pt.presheaf.obj (op V)`. Its definition and the following two laws do not
  require a limiting cone, compactness or spectrality; their proofs use only
  the preorder structure of the index.
- `colimit_ι_nativeCommRingCylinderSectionsComparison S i0 m U0 i`
  identifies its leg with `SheafedSpace.Γ.map` of the actual projection of
  the restricted cone, followed by the forward `restrict_Γ_obj` equality
  transport to sections on `V`.
- `originalStage_nativeCommRingCylinderSectionsComparison S i0 m U0 i`
  identifies the leg at `i` with the original projection component
  `(m.π.app (op i.1)).hom.c.app (op Ui)`, with the inverse stage restriction
  cast **before** the coprojection and the reverse cone-open equality cast
  **after** the original projection. The arrow identity is in `CommRingCat`.

For an actual limit `hm : IsLimit m`, assume every underlying original stage
is spectral, every original transition map is spectral, and
`IsCompact (U0 : Set (S.obj (op i0)))`. Then
`isIso_nativeCommRingCylinderSectionsComparison S i0 m U0 hm hstage
htransition hU0` proves this particular comparison is invertible. The
companion `exists_nativeCommRingCylinderSections_stage S i0 m U0 hm hstage
htransition hU0 r` gives, for any `r` on `V`, some `i : Set.Ici i0`
and section `a` on the **original** stage open `Ui` such that the original
projection, with the same reverse cone-open cast, maps `a` to `r`. For
example, apply it to a product `r * s` to represent that product on some
tail stage, without specifying which stage produces the witness.

There is no assumption that the opens or underlying spaces are inhabited, or
that the rings are nontrivial. Compact empty opens are permitted; the
some-stage theorem does **not** assert surjectivity of a fixed-stage map,
even at `i0`. The result concerns sheafed spaces valued in commutative rings,
not locally ringed spaces, scheme structure, or a chosen substitute for the
original cone.

The ring construction adapts the
[additive cylinder](NativeAdditiveCylinderSections.md) and the
[generic restricted-cylinder](NativeCylinderLimit.md) APIs, with ring
coefficients and the same actual original projections.
