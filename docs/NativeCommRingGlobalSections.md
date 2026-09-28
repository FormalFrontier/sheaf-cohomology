<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# Ring global sections of an original native spectral limit

Import `SheafCohomology.NativeCommRingGlobalSections` (or the aggregate
`SheafCohomology`) for theorems about the given native cone
`m : Cone S`, where
`S : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v}` and
`J : Type v` has `[SmallCategory J]`. For every original projection the
cocone `nativeCommRingGlobalSectionsCocone S m` has ring vertex
`SheafedSpace.Γ.obj (op m.pt)` and **literal** leg
`SheafedSpace.Γ.map (m.π.app (op i)).op`. Its comparison
`nativeCommRingGlobalSectionsComparison S m` is `colimit.desc` of this
cocone; `colimit_ι_nativeCommRingGlobalSectionsComparison` states exactly
that its composite with the `i`-th colimit injection is this original leg.
These definitions and stage equations need no limiting-cone, filtered,
spectral, nonempty-stage or surjectivity assumption.

## Invertibility and stage representatives

With `[IsFiltered J]`, `hm : IsLimit m`, spectral spaces at the **original**
stages of `S ⋙ SheafedSpace.forget CommRingCat` and spectral maps for its
**original** transitions, `isIso_nativeCommRingGlobalSectionsComparison`
proves the ring comparison invertible. It transports the *given* ring cone
through the [coefficient-forgetting limit theorem](CommRingForget.md),
compares its underlying Type projection mates with the existing Type-native
global-section comparison, and reflects the resulting isomorphism through
`CategoryTheory.forget CommRingCat`. The intermediate natural diagram
comparison and the colimit.post map are genuine isomorphisms, not an
assumed definitional equality of two colimit objects. For the induced
Type cone `Q` and point isomorphism `e`, the proof uses
`e.inv ≫ U.map (m.π.app (op i)) = Q.cone.π.app (op i)`, hence the actual
projection equations are retained.

`exists_nativeCommRingGlobalSections_stage` has the same filtered,
limiting and spectral hypotheses. For **each** ring section `r` at
`m.pt`, it gives **some** `i : J` and section `a` at `S.obj (op i)` with
`SheafedSpace.Γ.map (m.π.app (op i)).op a = r`. Its proof uses filtered
colimit joint surjectivity. This is **not** surjectivity from any chosen
fixed stage, nor a theorem for an empty filtered index. Neither result
assumes a section-surjectivity premise, nonempty stage spaces, or a
surjective transition map. The required same-universe and spectral
conditions cannot be discarded.

## Reproduction and attribution

The repository pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and officially published
spectral-stone-duality
`452b7b7be1bea76434cd083b1019a26f96b4ab30` in its toolchain and
eleven-package manifest. From this repository's root, obtain the matching
precompiled mathlib cache before building:

```sh
lake exe cache get
lake --wfail build SheafCohomology.NativeCommRingGlobalSections
lake --wfail build SheafCohomology SheafCohomologyExamples
```

These instructions are not a claim of a destination build or complete
private-inclusive axiom audit. Worker-a Hive Task
`hive-request-1c0851150518e166978e650f8b077bcdd9311334` (UID
`6ed601e1-657b-408f-bf75-7df21b10a83a`) authored the ring endpoint
and the relocated joint-stage theorem, adapting the published additive
endpoint by worker-a Hive Task
`hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004` (UID
`7b289efe-e184-4c33-9723-7ef39e977b59`). See
[credits](CREDITS.md) for bridge, planning and transfer attribution.
