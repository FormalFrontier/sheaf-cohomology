# Native cylinder sections after changing a principal tail

Import `SheafCohomology.NativeCylinderTailChange`. The producer
extends the coefficient-generic native cylinder sections in
`SheafCohomology.NativeCylinderOpenNaturality`; an ordinary-import
private example is `SheafCohomologyExamples.NativeCylinderTailChange`.

Fix one universe `v`, a directed preorder `ι : Type v`, a category
`C : Type (v + 1)` with `[Category.{v} C]`, and
`S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C`. Given `i0 j : ι`,
`h : i0 ≤ j`, and `U : Opens (S.obj (op i0))`, write
`V := stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)`. This **is** the inverse
image along the original transition `S.obj (op j) ⟶ S.obj (op i0)`, not
an arbitrary open known to be equal to it. All names below live in
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`.

## Tail and section diagrams

`betweenTailInclusion i0 j h : Set.Ici j ⥤ Set.Ici i0` sends `k` to
`⟨k.1, h.trans k.2⟩`; `betweenTailInclusion_final` proves that this functor
is final in every directed preorder. `stageOpen_betweenTail S i0 j h U k`
proves the **named** equality

```text
stageOpen S j V k = stageOpen S i0 U ((betweenTailInclusion i0 j h).obj k).
```

The equality is not definitional. The diagram-level iso
`cylinderSectionsTailIso S i0 j h U` has orientation

```text
cylinderSections S j V ≅
  betweenTailInclusion i0 j h ⋙ cylinderSections S i0 U.
```

It transports actual restricted native stages and their arrows, including
the transition square, rather than replacing them by a hypothetical common
open. `cylinderSectionsTailIso_hom_app` identifies its component with the
forward object-equality cast; `originalStage_cylinderSectionsTailIso` relates
that cast to the original presheaf's sections. The intermediate
`restrictedBetweenTailIso` and `namedRestrictCast_fac` expose the corresponding
native sheafed-space arrow and its monic open-inclusion characterization.

## Colimits and original cones

Only `[HasColimit (cylinderSections S i0 U)]` is required. The theorem
`hasColimit_cylinderSections_betweenTail` supplies the later colimit;
`hasColimit_cylinderSections_of_betweenTail` also transports existence in
the reverse direction. For a local goal needing later coprojections, use

```lean
letI := hasColimit_cylinderSections_betweenTail S i0 j h U
```

`cylinderSectionsTailColimitIso S i0 j h U` is the canonical composite of
the diagram NatIso's colimit iso and the final-functor colimit iso. Its law
`colimit_ι_cylinderSectionsTailColimitIso S i0 j h U k` says

```text
ι(cylinderSections S j V, k) ≫ T.hom =
  (cylinderSectionsTailIso S i0 j h U).hom.app k ≫
    ι(cylinderSections S i0 U, (betweenTailInclusion i0 j h).obj k).
```

For **any** original `m : Cone S`, `coneOpen_betweenTail S i0 j h U m`
proves `coneOpen S j m V = coneOpen S i0 m U`. There is no `IsLimit m`
requirement. Write `q` for the forward section-object `eqToHom` of this
equality. Then `cylinderSectionsComparison_betweenTail S i0 j h U m`
proves the actual commuting cone square:

```text
T.hom ≫ cylinderSectionsComparison S i0 m U =
  cylinderSectionsComparison S j m V ≫ q.
```

For example, with these hypotheses and `k : Set.Ici j`, one can precompose
this square by the actual coprojection and then by
`eqToHom (SheafedSpace.restrict_Γ_obj
  (S.obj (op k.1)) (stageOpen S j V k)).symm`. The private client theorem
`genericConeStageSquare` checks this original-stage equality. Its companion
`genericTailCoprojection` checks the coprojection before comparison;
`ringTailSquare` and `additiveTailSquare` rewrite the official ring and
additive comparisons using the accepted generic-comparison equalities.

The comparison arrows themselves are **not** claimed invertible. In
particular this module requires no compactness, spectrality, nonempty-open,
`Nontrivial`, chosen limit, or global all-opens cocompleteness assumption.
Identity/composition of successive tail changes and simultaneous variation
of `U` are separate possible coherence results, not claims here. This module
publicly imports the existing `SheafCohomology.NativeCylinderOpenNaturality`;
neither module requires a source-repository or incubator dependency.

This is a comparison for the actual transition-pullback open,
not an arbitrary equal open or an all-open isomorphism. See the
[open-naturality guide](NativeCylinderOpenNaturality.md) for the
underlying restricted-stage transformations.
