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

The original-open transport follows this library's
[additive-cylinder pattern](../SheafCohomology/NativeAdditiveCylinderSections.lean)
of worker-b Task `hive-request-581a9584fa061c70e8f8581b23cc51bae1d3f5bf`
(UID `0eb3d3fc-0bb3-4098-ab2f-892fe8a763f4`); the generic native
cylinder is by worker-a Task `hive-request-27d70680c0e69c147294098e3ac13b1c7092c0e1`
(UID `bfe6acf9-1385-4602-a9b8-1e88f6908b1a`), the spectral
restriction by worker-b Task `hive-request-e8a25d6c5328e70c571fe96c3ac0b8102530eaa1`
(UID `ddcebc71-0a10-45a6-b8cf-9606083d850e`), and the ring-global
theorem by worker-a Task `hive-request-1c0851150518e166978e650f8b077bcdd9311334`
(UID `6ed601e1-657b-408f-bf75-7df21b10a83a`). The latter adapts
additive-global work by `hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004`
(UID `7b289efe-e184-4c33-9723-7ef39e977b59`) and the CommRingForget
bridge by `hive-request-c57c813632815e9d350373cdfa7741657fb4852a`
(UID `2717d143-2755-441e-83fb-8f9190fbe8f1`). The API assessment is by
worker-b Task `hive-request-d3c2586e89c15b535aecaa643cab3e9cbdb8b549`
(UID `fc541648-a37d-4749-b741-30000d4baef2`). Named native-open
restrictions also reuse work of worker-a Tasks
`hive-request-dae0d04e8618b53de43730479c4033d21488695b` and
`hive-request-30271b71e726fc52aa0a7c7670ba0eca5de6eaac`;
the underlying ring-global plan was by
`hive-request-c122a6d40799b53667ffc3699a7642ef15453985`
(UID `911c1933-e837-4a1c-85cd-2dce903e2357`). This ring-cylinder
adaptation is by worker-a Task `hive-request-88dfae1c142ae9a97c6e943836f56272654fa848`
(UID `91101cdb-86bf-42a6-984d-2bd74e2d112a`).
