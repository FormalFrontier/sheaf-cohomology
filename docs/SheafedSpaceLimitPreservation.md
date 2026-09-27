# Preservation of native sheafed-space limits

Import `SheafCohomology.LimitPreservation` for two **named** witnesses in
`AlgebraicGeometry.SheafedSpace`:

```text
preservesLimitForgetOfSpaceCone A S c hc : PreservesLimit S (forget A)
preservesLimitForgetOfHasLimit A S : PreservesLimit S (forget A)
```

The aggregate `SheafCohomology` import also exposes these witnesses. The
private client leaf is registered in `SheafCohomologyExamples`; its imports
are not required to use the public API.

The first takes `S : Jᵒᵖ ⥤ SheafedSpace.{u,w,w} A`, an **actual** cone
`c : Cone (S ⋙ forget A)`, its `hc : IsLimit c`, and
`[HasWeakSheafify (Opens.grothendieckTopology c.pt) A]`. Coefficients
`A : Type u` carry `Category.{w} A`, a `FunLike` presentation of morphisms
on carriers `A → Type w`, `ConcreteCategory.{w} A`, limits and colimits,
preservation of limits and filtered colimits and reflection of isomorphisms
by `CategoryTheory.forget A`, plus `[HasColimitsOfShape J A]`.
The index `J : Type wj` has independent category morphism universe `vj`;
the hypotheses do not assert unrestricted limits of every diagram.
The explicit native universes are those of the prerequisite
`limitConeOfSpaceCone`; the shape object and morphism universes remain independent.

The proof calls `limitConeOfSpaceCone A S c hc`, whose `isLimit` proves the
**constructed** native cone limits. Its `limitConeOfSpaceCone_forget` identifies
the *entire* mapped native cone with the supplied limiting `c`, so `hc`
proves the mapped cone limits. Mathlib's
`CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone` transfers
this property from one native limiting cone to **every** native limiting
cone of `S`. This does not assume a native `HasLimit`, preservation,
reflection, or a converse about arbitrary native cones.

The second witness uses `[HasLimit (S ⋙ forget A)]` and
`[HasWeakSheafify (Opens.grothendieckTopology
((limit (S ⋙ forget A)) : TopCat)) A]`; it selects `limit.cone` and
`limit.isLimit` of the space diagram and applies the first theorem. Like
the prerequisite `hasLimitOfHasLimitForget`, it requires
`SheafedSpace.{u,w,w} A` and **does not register a global instance**.
Locally install it with `letI : PreservesLimit S (forget A) := ...` to use
`isLimitOfPreserves (forget A) hNative`, `preservesLimitIso`, and
`preservesLimitIso_hom_π` from mathlib. A native `IsLimit hNative` is only
the *input cone* to mathlib's generic preservation API, not a premise for
constructing either preservation witness.

`SheafCohomologyExamples.LimitPreservation` contains import-only private
clients: arbitrary diagrams over `(Fin 3)ᵒᵖ` for both `Type v` and
`AddCommGrpCat.{v}` use local preservation and `isLimitOfPreserves` on
arbitrary limiting native cones; their two distinct nonidentity index
arrows `0 ⟶ 1` and `1 ⟶ 2` check mapped-cone projection equations. The
Type client also invokes mathlib's chosen-limit comparison projection
after installing the existing named native-limit and new preservation
witnesses. An empty `PEmpty.{1}ᵒᵖ` diagram checks arbitrary native cones
and the chosen-base witness. No equality of arbitrary native spaces with
the selected base, or blanket empty-shape reflection, is claimed.

In the repository-pinned Lean/Lake environment, fetch matching mathlib
artifacts before focused checks:

```sh
lake exe cache get
LAKE_JOBS=1 LEAN_NUM_THREADS=2 lake --no-ansi --wfail build SheafCohomology.LimitPreservation SheafCohomologyExamples.LimitPreservation
printf 'import SheafCohomology.LimitPreservation\nset_option pp.universes true\n#check @AlgebraicGeometry.SheafedSpace.preservesLimitForgetOfSpaceCone\n#check @AlgebraicGeometry.SheafedSpace.preservesLimitForgetOfHasLimit\n' | lake env lean --stdin
```

## Provenance and lifecycle

The native construction prerequisite was authored by Worker A, Hive Task
`hive-request-700e4f0e3debb32b4538a1158e70ca099e66c254`, UID
`02943c65-933d-4b1e-974b-decbd5d5f153`, independently reviewed at
`c8a4369a1b025cd658807ebdaaa21084e6e5432c` and accepted by Anchor
as incubator commit `f30d2befa872ce170736d97a72444790847365e5`
in issue #4 comment 50401; it was **unregistered** at the original leaf's
acceptance. The original preservation leaf was authored by Worker B, Hive
Task `hive-request-502206a7e28d7384c6a1ab57a9acf7a38c6a9eb4`, UID
`5a505fe4-97ca-426f-8b06-9149e72762b3`, at incubator commit
`458297b9feef7fe8b838aa91db2944f53d23293a`. Fresh independent
review was by Worker A, Hive Task
`hive-request-7996da543adddee2f16c056f6551863372a81898`, UID
`4f167d3a-f251-4072-b17f-edabe055d33b`, at
`e7029896a2f9b3c22f0de6e118d6e6eb989f33a2:reviews/native-limit-preservation/REVIEW.md`;
Anchor accepted only that original leaf in incubator issue #4 comment
50907. It was **accepted but unregistered**, not integrated into
incubator main.

This source-exact destination adapter is by Worker A, distinct Hive Task
`hive-request-6d9e8f29fa46918f8089bb987efa7985c6f27b00`, UID
`6a32dd01-a3e7-451f-a859-bd1347902e71`. The destination contribution
starts from frozen, **unaccepted** sheaf-cohomology commit
`4baa42e7eb4336e0691501953f5273aefe229506`, not accepted current
main. Lean `leanprover/lean4:v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` remain pinned.
Anchor's later source-only aggregate registration preserves both Lean leaf
blobs and all dependency and CI files; it adds imports, navigation, credit and
metadata on this same frozen unaccepted predecessor. The destination leaf's
fresh independent review by Worker B Task
`hive-request-4e13230d0f0e11b815b6b11dd98d87e4dba4debd` (UID
`28835d9b-8899-4ce7-86ab-b206d5f5858a`), report
`ff72bdd17a803a20842c4bb564d4505ed8f01dc1`, approved only the three-file
transfer; it is separate from assessment of this registered graph.
Prerequisite and aggregate owner acceptance, applicable joined-graph checks,
protected integration and verified official publication remain pending.
This source-only registration supplies none of those missing checks. Only
after that publication may a separately reviewed
incubator conversion remove or replace the local implementation. No source
asset or source-specific coverage assertion is part of this reusable API.
