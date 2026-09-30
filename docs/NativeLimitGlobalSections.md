<!-- SPDX-License-Identifier: Apache-2.0 -->
# Global sections of a chosen native sheafed-space limit

`SheafCohomology.NativeLimitGlobalSections` compares the colimit of the
**actual native stage global sections** with global sections of a chosen
native sheafed-space limit. Import this module directly or use the aggregate
`SheafCohomology` public root. It is a reusable mathematical API, not a
source-passage or source-coverage claim.

## Exact data and maps

Fix `J : Type v` with `[SmallCategory J]` and `[IsFiltered J]`, a diagram
`N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} (Type v)`, and an
*actual* underlying-space cone
`c : Cone (N ⋙ SheafedSpace.forget (Type v))` with `hc : IsLimit c`.
The native limit is the existing
`Q := SheafedSpace.limitConeOfSpaceCone (Type v) N c hc`. The statement
uses the same universe `v` for the small filtered index, spaces and
Type-valued sheaves. Write `S := N.rightOp ⋙ SheafedSpace.Γ` only as an
abbreviation, not a replacement diagram.

`AlgebraicGeometry.SheafedSpace.nativeGlobalSectionsCocone N c hc : Cocone S`
has vertex `SheafedSpace.Γ.obj (op Q.cone.pt)` and stage legs exactly

```lean
SheafedSpace.Γ.map (Q.cone.π.app (op i)).op
```

`nativeGlobalSectionsComparison N c hc` is the actual
`colimit.desc _ (nativeGlobalSectionsCocone N c hc)`. Its projection law
`colimit_ι_nativeGlobalSectionsComparison N c hc i` says

```lean
colimit.ι S i ≫ nativeGlobalSectionsComparison N c hc =
  SheafedSpace.Γ.map (Q.cone.π.app (op i)).op
```

The factorization `nativeGlobalSectionsComparison_eq_colimMap_post N c hc`
identifies **this** descended map with

```lean
colimMap (SheafCohomology.ConePullbackSections.coneSections N c) ≫
  colimit.post (SheafedSpace.conePullback (Type v) N c)
    (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt))
```

Here the proof installs *locally* the same
`CategoryTheory.Sheaf.instHasColimitsOfShape` for `c.pt.Sheaf (Type v)`
used in the native construction. It compares each coprojection via the
published cone-pullback section leg, official
`limitConeOfSpaceCone_π_mate_colimit_ι`, the sheaf adjunction unit and
`sheafMate_adjoint`, then applies `colimit.hom_ext`. The codomain remains
`Γ(Q.cone.pt)`; no alternate native limit or arbitrary colimit-choice
identification is substituted.

For the isomorphism, additionally assume exactly

```lean
hstage : ∀ k : Jᵒᵖ,
  SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k)
htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
  IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)
```

The named theorem
`isIso_nativeGlobalSectionsComparison N c hc hstage htransition`
proves `IsIso (nativeGlobalSectionsComparison N c hc)`, not a global
instance. It composes the moving-stage
`isIso_colimMap_coneSections` with the fixed-base
`CompactOpenSections.canonicalSectionsComparison_isIso` at the compact
top open. Official `SpectralStoneDuality.Limits` supplies compactness,
prespectrality and quasi-separatedness of the cofiltered spectral-space
limit; `hc.conePointUniqueUpToIso` and `TopCat.homeoOfIso` transfer them
to `c.pt`. No desired-`IsIso`, inhabited-stage, cover or alternate-limit
premise is assumed.

`SheafCohomologyExamples.NativeLimitGlobalSections` uses an **ordinary**
`import SheafCohomology.NativeLimitGlobalSections`. Its theorem
`nativeProjections_detect_coprojection_eq` is a private client declaration:
equality of two actual projection images implies equality of the two
colimit coprojections by the stated projection law and cancellation of
the named isomorphism. Neither `import all` nor a public wrapper is needed
for downstream use.
