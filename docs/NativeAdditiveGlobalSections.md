# Native additive global sections of filtered spectral limits

For a small category `J`, an additive sheafed-space diagram
`S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat`, and **any chosen cone** `m : Cone S`,
`AlgebraicGeometry.SheafedSpace.nativeAdditiveGlobalSectionsCocone S m`
has vertex `Γ.obj (op m.pt)` and leg at `i : J` exactly
`Γ.map (m.π.app (op i)).op`. Its naturality is the triangle identity of `m`;
no limiting or spectral assumption is used. The morphism
`nativeAdditiveGlobalSectionsComparison S m` is the additive colimit's
`colimit.desc` of this cocone. The theorem
`colimit_ι_nativeAdditiveGlobalSectionsComparison S m i` identifies the
composite of the original stage coprojection with the comparison as the
global-section map of the original cone projection. The inferred signatures
of the cocone, comparison and stage law do not require `IsFiltered J`, a
limit witness `hm`, or spectral hypotheses, even though their source module
declares filteredness for its later isomorphism theorem.

If `J` is filtered, `hm : IsLimit m`, every original stage space of
`S ⋙ SheafedSpace.forget AddCommGrpCat` is spectral, and every original
transition of that space diagram is a spectral map, then
`isIso_nativeAdditiveGlobalSectionsComparison S m hm hstage htransition`
proves the comparison is an isomorphism. There is **no** assumption of
surjective transitions, injective projections, an already-invertible map,
nonempty opens, or an independently supplied limit of restrictions. The
statement keeps the original cone, including its original projections.

The proof first obtains a limiting space cone by applying
`SheafedSpace.preservesLimitForgetOfHasLimit` to `hm`. It obtains a Type-valued
native limiting cone independently from
`SheafedSpace.AbelianForget.preservesCofilteredLimit S`; the official
`underlying_mapCone_forget` and `underlyingDiagram_forget` identify the full
space cones and functors, not just their carrier objects. Let `Q` be
`limitConeOfSpaceCone` of the forgotten diagram and actual space cone. The
unique cone-point iso `e : underlying.obj m.pt ≅ Q.cone.pt` satisfies
`e.inv ≫ (underlying.mapCone m).π.app (op i) = Q.cone.π.app (op i)`.

On sections, the identity-component natural iso
`nativeAdditiveGammaDiagramForgetIso` (kept private) compares the forgotten
additive Γ diagram with the actual Type Γ diagram. Its components reduce,
by `Γ_obj_op` and `underlying_obj_presheaf`, to the same `op ⊤` sections.
Naturality and the projection case reduce, by `Γ_map_op`,
`underlying_map_c`, and the component of `whiskerRight`, to the underlying
map of the **original** additive `f.hom.c.app (op ⊤)`; the Lean proof
exhibits this common component before applying reflexivity. Thus the
identity-on-sections iso at `m.pt` and the diagram iso transport original
projections without substituting another cone.

Let `A = S.rightOp ⋙ Γ`, `F = forget AddCommGrpCat`, `N = S ⋙ underlying`,
`D = N.rightOp ⋙ Γ`, `q` be the diagram-induced colimit iso, and `t` the
vertex section iso. The Type-valued arrow compared to the existing native
Type comparison is

```text
q.inv ≫ colimit.post A F ≫ F.map (nativeAdditiveGlobalSectionsComparison S m)
  ≫ t.hom ≫ Γ.map e.inv.op.
```

The *forward* direction of `colimit.post` is essential. Colimit extensionality
reduces equality to each stage: `HasColimit.ι_isoOfNatIso_inv_assoc`,
`colimit.ι_post_assoc`, and the new additive stage law yield the forgotten
actual projection; the section-map compatibility turns it into the Type
projection; `e.inv` turns it into `Q`'s projection. The already-proved
`isIso_nativeGlobalSectionsComparison N c hc` supplies the Type isomorphism;
filtered colimit preservation by `F` and reflection of isomorphisms by `F`
cancel the other comparison isomorphisms. This proof does not repeat the
underlying spectral, compactness, gluing, or local section arguments.

`SheafCohomologyExamples.NativeAdditiveGlobalSections` is an
ordinary-import client. Its theorem `nativeProjection_eq_iff_eventually_eq`
states that two sections at one *original* additive stage agree under the
original projection to `m.pt` if and only if an original transition sends
them to equal sections at some later stage. Its proof applies the new
comparison's injectivity and exact stage law; the explicit
`isColimitOfPreserves` witness for `F.mapCocone` then invokes
`Types.FilteredColimit.isColimit_eq_iff'` on the forgotten actual colimit.
Conversely it maps the resulting equality of original additive
coprojections through the new comparison. No eventual-equality hypothesis
is fed into this client.
