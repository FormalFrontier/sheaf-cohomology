# Native limits of principal-tail open cylinders

Import `SheafCohomology.NativeCylinderLimit` for the API in
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`. The separate
`SheafCohomologyExamples.NativeCylinderLimit` (Type-valued) and
`SheafCohomologyExamples.NativeCylinderLimitAdditive` (additive-valued) are
ordinary-import clients. None imports the incubator or a source-research
repository.

Let `ι : Type v` be a preorder with `IsDirectedOrder ι`, let `i0 : ι` be an
**explicit** distinguished index, and let `C : Type (v + 1)` carry
`[Category.{v} C]`, inferred from
`N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C`. Given a native cone
`m : Cone N`, its native limit witness `hm : IsLimit m`, and an arbitrary
`U0 : Opens (N.obj (op i0))`, the principal construction is

```lean
restrictedIsLimit N i0 m hm U0 :
  IsLimit (restrictedCone N i0 m U0)
```

Here `restricted N i0 U0` is the actual functor of **native sheafed-space
restrictions** over `(Set.Ici i0)ᵒᵖ`; `restrictedCone N i0 m U0` is its
canonical cone, with point literally
`m.pt.restrict (coneOpen N i0 m U0).isOpenEmbedding`. No limit of the
restricted diagram is assumed. There is no linear-order hypothesis, nor any
nonempty-space or nonempty-open hypothesis.

## Constructions and use

- `tailInclusion i0 : Set.Ici i0 ⥤ ι` is final by directedness, and
  `tailInclusion_op_initial` makes its opposite initial. The public
  `tailDirectedOrder i0 : IsDirectedOrder (Set.Ici i0)` exposes the same
  former private witness for *local* filtered-tail use; it installs no
  global instance. `tailDiagram N i0` restricts the original diagram to
  this opposite tail.
- `transition N i0 i` maps tail stage `i` to the distinguished stage;
  `stageOpen N i0 U0 i` is the inverse image of `U0` under this transition.
  `stageOpen_map` supplies the equality of named inverse-image opens needed
  for each arrow `stageMap N i0 U0 f`. `restricted N i0 U0` comprises these
  literal restrictions and native arrows. `inclusion N i0 U0` is their
  natural transformation to the original tail diagram.
- `coneOpen N i0 m U0` pulls `U0` back along the actual projection at `i0`.
  `coneOpen_eq_stage` identifies it with the inverse image of each stage
  open; `stageOpen_base` identifies the distinguished-stage open with `U0`.
  `coneComponent` uses the named-preimage native restriction arrow, and
  `coneComponent_fac` records its commuting native inclusion square. The
  private naturality helper proves full native-arrow cone naturality.
- `tailIsLimit N i0 m hm` transfers the original limit along the initial
  opposite tail. For any `t : Cone (restricted N i0 U0)`, the arrow
  `originalLift N i0 m hm U0 t : t.pt ⟶ m.pt` satisfies
  `originalLift_fac`; `originalLift_range` proves it lands in `coneOpen`,
  even for empty spaces and opens. `restrictedLift` factors that arrow through
  the actual native open restriction, with `restrictedLift_fac` and
  `restrictedLift_component` establishing the native cone equations. Monic
  cancellation proves uniqueness in `restrictedIsLimit`. No preservation of
  native limits by the underlying topological-space functor is asserted.

The private theorem `lift_original_projection` in the ordinary-import client
`SheafCohomologyExamples.NativeCylinderLimit` specializes to `C = Type v`,
takes *any* `t : Cone (restricted N i0 U0)` and any tail stage
`i : Set.Ici i0`, applies `(restrictedIsLimit N i0 m hm U0).lift t`, and
recovers its original-projection equation after composing with the native
restriction inclusion. It neither posits the desired restricted `IsLimit`
nor replaces the diagram with an alternate model.

The separate private theorem `lift_original_projection` in the ordinary-import
`SheafCohomologyExamples.NativeCylinderLimitAdditive` specializes the **same**
constructed limit to `C = AddCommGrpCat.{v}`. For arbitrary `m`, `hm`, `U0`,
restricted cone `t` and tail stage `i`, it proves the full sheafed-space arrow
equality

```lean
((restrictedIsLimit N i0 m hm U0).lift t ≫
    m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding) ≫
      m.π.app (op i.1) =
  t.π.app (op i) ≫ (inclusion N i0 U0).app (op i)
```

The additive client assumes no restricted limit and proves no chosen-limit
comparison or reflection statement.
