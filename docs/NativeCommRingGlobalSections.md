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
