# Forgetting native additive cone cocones

Import `SheafCohomology.AbelianForget.ConePullbackCocone` for the three public
declarations in `AlgebraicGeometry.SheafedSpace.AbelianForget`. This focused
module publicly imports `SheafCohomology.AbelianForget.ConePullback` and
`SheafCohomology.ConePullbackCocone`. The aggregate `SheafCohomology`
re-exports it; the examples root imports its private client module.

Take any `J : Type wj` with `[Category.{vj} J]`, a diagram
`S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}`, and an **actual** native cone
`c : Cone S`. Let `cA := (SheafedSpace.forget AddCommGrpCat.{v}).mapCone c`,
`cT := underlying.mapCone c`, `U := underlyingSheaf (c.pt : TopCat)`, and
`θ := conePullbackIso S cA`. The independent index object and morphism
universes are `wj` and `vj`; `v` is the sheaf/coefficient universe.

- `underlying_mapCone_forget S c` identifies
  `(SheafedSpace.forget (Type v)).mapCone cT = underlyingCone S cA`
  *strictly*, by `rfl`. The vertex and projection arrows are unchanged.
- `conePullbackCocone_forget_ι S c i`, for any `i : J`, identifies the
  Type-valued native cocone leg with
  `θ.hom.app i ≫ U.map ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app i)`.
  Here the Type-valued cocone is
  `SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) cT`.
  The stage law uses the mate of the *actual* projection `c.π.app (op i)`.
- `conePullbackCocone_forget_desc S c` needs precisely three ordinary
  colimit witnesses: `[HasColimit DA]`, `[HasColimit (DA ⋙ U)]`, and
  `[HasColimit DT]`, where
  `DA := SheafedSpace.conePullback AddCommGrpCat.{v} S cA` and
  `DT := SheafedSpace.conePullback (Type v) (S ⋙ underlying)
    ((SheafedSpace.forget (Type v)).mapCone cT)`.
  Writing `KA := SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c`
  and `KT := SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) cT`,
  its exact canonical comparison equation is:

  ```text
  (colimMap θ.hom ≫ colimit.post DA U) ≫ U.map (colimit.desc DA KA)
    = colimit.desc DT KT.
  ```

The private `conePullbackCocone_forget_desc_canonical` transports the actual
diagram colimit witnesses to the canonical pullback comparison and proves the
desc equation by `colimit.post_desc`, `colimit.map_desc`, `colimit.hom_ext`,
`colimit.ι_desc`, and the stage law. No colimiting cocone, limiting native
cone, filteredness, nonempty index, stage isomorphism, or endpoint
invertibility is assumed or obtained. The private import-only clients in
`SheafCohomologyExamples.AbelianForgetConePullbackCocone` exercise all three
`Fin 3` stages, two nonidentity **index** arrows, the three explicit colimit
witnesses, and a native cone with literal empty carrier. Their local
same-universe filtered specialization establishes invertibility only of
`colimMap θ.hom ≫ colimit.post DA U`, using existing results; arrow images
may still be identities and neither desc-to-vertex map is claimed invertible.

## Expression provenance

The original Lean expressions are by Worker B Hive Task
`hive-request-411a3aeeefaf41c928ba5dd589f2d14811f0a38e`, UID
`8a86b77b-9e0d-48a9-9bda-4d79884fb698`; source expression revision
`3af55bc102c0c81f20271560877d11d786e7ca43`, production blob
`63f5406ad1da99f21143b40a294c06e303f94aad`, client blob
`8ca578fae76d2a0cd3bf66316dc041b1256d17d3`. This destination
adaptation is by Worker B Hive Task
`hive-request-fadb8a219b9546f83011af5ec4651e9475d1c1de`, UID
`a79502b5-a697-474a-b3f5-1e42c062fe22`. This guide documents a
registered destination API, not protected integration, publication, an endpoint
theorem, or source-specific correspondence/coverage. Existing construction
and comparison credits remain in their respective destination files.
