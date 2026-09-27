# Historical native-generated sheaf-cohomology API (26 modules)

Lake development package version `0.1.0`; analyzed source: `a9f1a38787d33205c469ff89710563fffb4974fd`; native doc-gen4: `97d4ecdfc8e09e7f511724c25e303d448de6a3db`.
This frozen 556-site reference covers the original 24 subject modules and two
root/client modules at the analyzed revision, not the eleven later subjects or
their ten private client modules. The new declarations have lightweight
supplemental references indexed in the [current module guide](Guide.md).
The old source hashes and manifest are historical, not a fresh attestation of
the current 47-module tree. Its `api_sha256` checks the original generated
Markdown **before this explanatory introduction was updated**, not the bytes
of this editorially amended file.
These are native **display signatures**, not complete elaboration-ready declarations
or a proof/axiom census. Namespace resolution, inferred types and universes can be
suppressed by native pretty-printing; follow each frozen source link for the exact
binders and proof. Private helpers/examples need a separate complete proof audit.
Twelve rows are marked **Source-local instance registration**: they are not
globally registered typeclass instances, even if the native header says `theorem`.
Explicit-name visibility is distinct from local typeclass registration.
[Module guide](Guide.md) · [Historical reproduction](README.md) ·
[Credits](CREDITS.md) · [Input manifest](api-manifest.json).

## `SheafCohomology.AcyclicResolution`

Scope: subject module.

<a id="api-285f018732adab5f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} {f : A ⟶ B} (R' : AcyclicResolution X B) (φ : R.Hom R' f) (q : ℕ) (hq : 0 < q) (x : Ext X A q) : (R'.extPositiveIsoHomology q hq) (x.comp (mk₀ f) ⋯) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (R.homComplexMap R' φ.hom) q)) ((R.extPositiveIsoHomology q hq) x)
```

**Native source docstring:**

The positive-degree Ext comparison is natural in maps of acyclic
resolutions.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L691-L712) · native range starts at 691.

<a id="api-684d0e252ef32e2b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (q : ℕ) (hq : 0 < q) : Ext X A q ≃+ ↑(HomologicalComplex.homology R.homComplex q)
```

**Native source docstring:**

Positive-degree Ext of the resolved object is canonically the homology of
the additive coyoneda complex of any acyclic resolution.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L676-L689) · native range starts at 676.

<a id="api-9c7a1fb6c1bd1552"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality_apply {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) (x : ↑(Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))))) : (R'.extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (R.extZeroCokernelMap R' f n)) x) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) (n + 1))) ((R.extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv x)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L663-L674) · native range starts at 663.

<a id="api-cbf6a90ae1efffd1"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology R'.extZeroComplex (n + 1) ⟶ Z) : CategoryStruct.comp (R.extZeroCokernelMap R' f n) (CategoryStruct.comp (R'.extZeroCokernelIsoHomology n).hom h) = CategoryStruct.comp (R.extZeroCokernelIsoHomology n).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) (n + 1)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L647-L647) · native range starts at 647.

<a id="api-a6c104e74187a2cb"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology_hom_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : CategoryStruct.comp (R.extZeroCokernelMap R' f n) (R'.extZeroCokernelIsoHomology n).hom = CategoryStruct.comp (R.extZeroCokernelIsoHomology n).hom (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) (n + 1))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L647-L661) · native range starts at 647.

<a id="api-3f2c0fa0ec5fc92e"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality_apply {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] (x : Ext X (HomologicalComplex.cycles R.cocomplex n) 1) : (R'.cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm (x.comp (mk₀ (HomologicalComplex.cyclesMap f n)) ⋯) = (ConcreteCategory.hom (R.extZeroCokernelMap R' f n)) ((R.cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm x)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L633-L645) · native range starts at 633.

<a id="api-cb5ff8cf07a7c760"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] {Z : AddCommGrpCat} (h : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R'.cocomplex n (n + 1))) ⟶ Z) : CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X ⋯)) (CategoryStruct.comp (R'.cyclesCokernelIso n).inv h) = CategoryStruct.comp (R.cyclesCokernelIso n).inv (CategoryStruct.comp (R.extZeroCokernelMap R' f n) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L619-L619) · native range starts at 619.

<a id="api-79a05cb3a5888172"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_inv_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] : CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X ⋯)) (R'.cyclesCokernelIso n).inv = CategoryStruct.comp (R.cyclesCokernelIso n).inv (R.extZeroCokernelMap R' f n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L619-L631) · native range starts at 619.

<a id="api-935b751206bc4433"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_hom_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] {Z : AddCommGrpCat} (h : ↧(Ext X (HomologicalComplex.cycles R'.cocomplex n) 1) ⟶ Z) : CategoryStruct.comp (R.extZeroCokernelMap R' f n) (CategoryStruct.comp (R'.cyclesCokernelIso n).hom h) = CategoryStruct.comp (R.cyclesCokernelIso n).hom (CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X ⋯)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L603-L603) · native range starts at 603.

<a id="api-9281c21103701e40"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso_hom_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] : CategoryStruct.comp (R.extZeroCokernelMap R' f n) (R'.cyclesCokernelIso n).hom = CategoryStruct.comp (R.cyclesCokernelIso n).hom (AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X ⋯))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L603-L617) · native range starts at 603.

<a id="api-e8169a5222ba7ad8"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelMap {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))) ⟶ Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R'.cocomplex n (n + 1)))
```

**Native source docstring:**

The map of dimension-shift cokernels induced by a map of resolution
complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L590-L601) · native range starts at 590.

<a id="api-4b4425d1adb626c6"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_extZeroCokernelIsoHomology_hom_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_extZeroCokernelIsoHomology_hom_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology R.extZeroComplex (n + 1) ⟶ Z) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1)))) (CategoryStruct.comp (R.extZeroCokernelIsoHomology n).hom h) = CategoryStruct.comp (R.extZeroCyclesIso (n + 1)).inv (CategoryStruct.comp (HomologicalComplex.homologyπ R.extZeroComplex (n + 1)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L580-L580) · native range starts at 580.

<a id="api-90061e4b76dd6cc7"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_extZeroCokernelIsoHomology_hom`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_extZeroCokernelIsoHomology_hom {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1)))) (R.extZeroCokernelIsoHomology n).hom = CategoryStruct.comp (R.extZeroCyclesIso (n + 1)).inv (HomologicalComplex.homologyπ R.extZeroComplex (n + 1))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L580-L588) · native range starts at 580.

<a id="api-2ee13703eb763d30"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCokernelIsoHomology {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))) ≅ HomologicalComplex.homology R.extZeroComplex (n + 1)
```

**Native source docstring:**

The cokernel arising in the degree-one dimension shift is canonically the
homology of the degree-zero Ext complex in the next degree.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L549-L578) · native range starts at 549.

<a id="api-07cdc39a13725153"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesCokernelIso {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)] : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))) ≅ ↧(Ext X (HomologicalComplex.cycles R.cocomplex n) 1)
```

**Native source docstring:**

The dimension-shift cokernel is canonically the degree-one Ext group of
the cycles in the same degree.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L540-L547) · native range starts at 540.

<a id="api-bec528e17632056c"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZero_toCycles_mapCyclesIso_hom_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZero_toCycles_mapCyclesIso_hom_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) {Z : AddCommGrpCat} (h : (extFunctorObj X 0).obj (HomologicalComplex.cycles R.cocomplex (n + 1)) ⟶ Z) : CategoryStruct.comp (HomologicalComplex.toCycles R.extZeroComplex n (n + 1)) (CategoryStruct.comp (R.extZeroCyclesIso (n + 1)).hom h) = CategoryStruct.comp ((extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L529-L529) · native range starts at 529.

<a id="api-b8211f1463797964"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZero_toCycles_mapCyclesIso_hom`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZero_toCycles_mapCyclesIso_hom {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : CategoryStruct.comp (HomologicalComplex.toCycles R.extZeroComplex n (n + 1)) (R.extZeroCyclesIso (n + 1)).hom = (extFunctorObj X 0).map (HomologicalComplex.toCycles R.cocomplex n (n + 1))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L529-L538) · native range starts at 529.

<a id="api-1e45a381beb38138"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_inv_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_inv_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.cycles R'.extZeroComplex n ⟶ Z) : CategoryStruct.comp ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n)) (CategoryStruct.comp (R'.extZeroCyclesIso n).inv h) = CategoryStruct.comp (R.extZeroCyclesIso n).inv (CategoryStruct.comp (HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L518-L518) · native range starts at 518.

<a id="api-201f63a5ece1c513"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_inv_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_inv_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : CategoryStruct.comp ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n)) (R'.extZeroCyclesIso n).inv = CategoryStruct.comp (R.extZeroCyclesIso n).inv (HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L518-L527) · native range starts at 518.

<a id="api-e7baaee04c1ca110"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) {Z : AddCommGrpCat} (h : (extFunctorObj X 0).obj (HomologicalComplex.cycles R'.cocomplex n) ⟶ Z) : CategoryStruct.comp (HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n) (CategoryStruct.comp (R'.extZeroCyclesIso n).hom h) = CategoryStruct.comp (R.extZeroCyclesIso n).hom (CategoryStruct.comp ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L504-L504) · native range starts at 504.

<a id="api-064166f4e30368fc"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : CategoryStruct.comp (HomologicalComplex.cyclesMap (R.extZeroComplexMap R' f) n) (R'.extZeroCyclesIso n).hom = CategoryStruct.comp (R.extZeroCyclesIso n).hom ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f n))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L504-L516) · native range starts at 504.

<a id="api-bc1b9eb3dfffa0ea"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_map_iCycles_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_map_iCycles_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) {Z : AddCommGrpCat} (h : (extFunctorObj X 0).obj (R.cocomplex.X n) ⟶ Z) : CategoryStruct.comp (R.extZeroCyclesIso n).hom (CategoryStruct.comp ((extFunctorObj X 0).map (HomologicalComplex.iCycles R.cocomplex n)) h) = CategoryStruct.comp (HomologicalComplex.iCycles R.extZeroComplex n) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L496-L496) · native range starts at 496.

<a id="api-783bc615f29e75a2"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_map_iCycles`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso_hom_map_iCycles {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : CategoryStruct.comp (R.extZeroCyclesIso n).hom ((extFunctorObj X 0).map (HomologicalComplex.iCycles R.cocomplex n)) = HomologicalComplex.iCycles R.extZeroComplex n
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L496-L502) · native range starts at 496.

<a id="api-614aa449c8d65745"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCyclesIso {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : HomologicalComplex.cycles R.extZeroComplex n ≅ (extFunctorObj X 0).obj (HomologicalComplex.cycles R.cocomplex n)
```

**Native source docstring:**

Degree-zero Ext preserves the cycle kernel of a resolution complex.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L488-L494) · native range starts at 488.

<a id="api-64749963a19870e8"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomology_eqToIso_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomology_eqToIso_naturality_apply {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) {m n : ℕ} (h : m = n) (x : ↑(HomologicalComplex.homology R.extZeroComplex m)) : (eqToIso ⋯).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) m)) x) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n)) ((eqToIso ⋯).addCommGroupIsoToAddEquiv x)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L477-L486) · native range starts at 477.

<a id="api-6a80ba84e9b100bd"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality_apply {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) (x : ↑(HomologicalComplex.homology R.extZeroComplex n)) : (R'.extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n)) x) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (R.homComplexMap R' f) n)) ((R.extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv x)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L465-L475) · native range starts at 465.

<a id="api-57c48dbf7e1e82f0"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology R'.homComplex n ⟶ Z) : CategoryStruct.comp (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n) (CategoryStruct.comp (R'.extZeroHomologyIsoHomology n).hom h) = CategoryStruct.comp (R.extZeroHomologyIsoHomology n).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (R.homComplexMap R' f) n) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L452-L452) · native range starts at 452.

<a id="api-dbaa7ee5d7a5b996"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology_hom_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : CategoryStruct.comp (HomologicalComplex.homologyMap (R.extZeroComplexMap R' f) n) (R'.extZeroHomologyIsoHomology n).hom = CategoryStruct.comp (R.extZeroHomologyIsoHomology n).hom (HomologicalComplex.homologyMap (R.homComplexMap R' f) n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L452-L463) · native range starts at 452.

<a id="api-53595f42bef08afb"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroHomologyIsoHomology {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) (n : ℕ) : HomologicalComplex.homology R.extZeroComplex n ≅ HomologicalComplex.homology R.homComplex n
```

**Native source docstring:**

The induced canonical isomorphism on homology.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L447-L450) · native range starts at 447.

<a id="api-ba0735a773c15663"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex_hom_naturality_assoc {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) {Z : CochainComplex AddCommGrpCat ℕ} (h : R'.homComplex ⟶ Z) : CategoryStruct.comp (R.extZeroComplexMap R' f) (CategoryStruct.comp R'.extZeroComplexIsoHomComplex.hom h) = CategoryStruct.comp R.extZeroComplexIsoHomComplex.hom (CategoryStruct.comp (R.homComplexMap R' f) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L439-L439) · native range starts at 439.

<a id="api-ebe502f5a366938a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex_hom_naturality {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) : CategoryStruct.comp (R.extZeroComplexMap R' f) R'.extZeroComplexIsoHomComplex.hom = CategoryStruct.comp R.extZeroComplexIsoHomComplex.hom (R.homComplexMap R' f)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L439-L445) · native range starts at 439.

<a id="api-ab9a4f92d8fa95d9"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexIsoHomComplex {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) : R.extZeroComplex ≅ R.homComplex
```

**Native source docstring:**

The termwise degree-zero Ext complex is canonically isomorphic to the
additive coyoneda complex.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L432-L437) · native range starts at 432.

<a id="api-2c642fa5aa27260a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.homComplexMap`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.homComplexMap {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) : R.homComplex ⟶ R'.homComplex
```

**Native source docstring:**

A map of resolutions induces a map on the additive coyoneda complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L426-L430) · native range starts at 426.

<a id="api-575b2d4b225bf2cb"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexMap`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplexMap {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) {B : D} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) : R.extZeroComplex ⟶ R'.extZeroComplex
```

**Native source docstring:**

A map of resolutions induces a map on the degree-zero Ext complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L421-L424) · native range starts at 421.

<a id="api-6b9e0332cccc8bb5"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.homComplex`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.homComplex {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

The additive coyoneda functor applied termwise to an acyclic resolution.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L416-L419) · native range starts at 416.

<a id="api-bda580d5039f854b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplex`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroComplex {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] {X A : D} (R : AcyclicResolution X A) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

The degree-zero Ext functor applied termwise to an acyclic resolution.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L412-L414) · native range starts at 412.

<a id="api-045022f866759bfb"></a>

### `CategoryTheory.Abelian.Ext.instPreservesFiniteLimitsAddCommGrpCatExtFunctorObjOfNatNat_sheafCohomology`

```lean
instance CategoryTheory.Abelian.Ext.instPreservesFiniteLimitsAddCommGrpCatExtFunctorObjOfNatNat_sheafCohomology {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] (X : D) : Limits.PreservesFiniteLimits (extFunctorObj X 0)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L405-L406) · native range starts at 405.

<a id="api-4e6370e40168f01c"></a>

### `CategoryTheory.Abelian.Ext.extZeroCoyonedaIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.extZeroCoyonedaIso {D : Type u} [Category.{v, u} D] [Abelian D] [HasExt D] (X : D) : extFunctorObj X 0 ≅ preadditiveCoyoneda.obj (Opposite.op X)
```

**Native source docstring:**

Degree-zero Ext, as a functor in its second variable, is canonically the
preadditive coyoneda functor.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L390-L403) · native range starts at 390.

<a id="api-faf296c3bbc30f44"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate_symm_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate_symm_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n q : ℕ) (hq : 0 < q) (x : Ext X (HomologicalComplex.cycles R.cocomplex 0) (n + q)) : (R'.cyclesDimensionShiftIterate n q hq).symm (x.comp (mk₀ (HomologicalComplex.cyclesMap f 0)) ⋯) = ((R.cyclesDimensionShiftIterate n q hq).symm x).comp (mk₀ (HomologicalComplex.cyclesMap f n)) ⋯
```

**Native source docstring:**

The inverse iterated dimension shift is natural in maps of resolution
complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L370-L382) · native range starts at 370.

<a id="api-a6ed38c072288e94"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n q : ℕ) (hq : 0 < q) (x : Ext X (HomologicalComplex.cycles R.cocomplex n) q) : (R'.cyclesDimensionShiftIterate n q hq) (x.comp (mk₀ (HomologicalComplex.cyclesMap f n)) ⋯) = ((R.cyclesDimensionShiftIterate n q hq) x).comp (mk₀ (HomologicalComplex.cyclesMap f 0)) ⋯
```

**Native source docstring:**

The iterated dimension shift is natural in maps of resolution complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L352-L368) · native range starts at 352.

<a id="api-e377241617b1520e"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShiftIterate {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n q : ℕ) : 0 < q → Ext X (HomologicalComplex.cycles R.cocomplex n) q ≃+ Ext X (HomologicalComplex.cycles R.cocomplex 0) (n + q)
```

**Native source docstring:**

Iterating the canonical dimension shifts moves Ext of degree-`n` cycles
back to Ext of the degree-zero cycles.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L341-L350) · native range starts at 341.

<a id="api-71b18f05ed30245f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShift_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShift_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n q : ℕ) (hq : 0 < q) (x : Ext X (HomologicalComplex.cycles R.cocomplex (n + 1)) q) : (R'.cyclesDimensionShift n q hq) (x.comp (mk₀ (HomologicalComplex.cyclesMap f (n + 1))) ⋯) = ((R.cyclesDimensionShift n q hq) x).comp (mk₀ (HomologicalComplex.cyclesMap f n)) ⋯
```

**Native source docstring:**

Dimension shift along cycle short exact sequences is natural in a map of
resolution complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L320-L332) · native range starts at 320.

<a id="api-9b39d4fbeca264dd"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShift`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesDimensionShift {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n q : ℕ) (hq : 0 < q) : Ext X (HomologicalComplex.cycles R.cocomplex (n + 1)) q ≃+ Ext X (HomologicalComplex.cycles R.cocomplex n) (q + 1)
```

**Native source docstring:**

One dimension shift along the canonical cycle short exact sequence.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L310-L318) · native range starts at 310.

<a id="api-648b36539534dc7b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplex_shortExact`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplex_shortExact {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n : ℕ) : (R.cyclesShortComplex n).ShortExact
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L282-L308) · native range starts at 282.

<a id="api-bd0ca85a9dad53cc"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap_comp`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap_comp {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {X' A' X'' A'' : C} {R' : AcyclicResolution X' A'} {R'' : AcyclicResolution X'' A''} (f : R.cocomplex ⟶ R'.cocomplex) (g : R'.cocomplex ⟶ R''.cocomplex) (n : ℕ) : R.cyclesShortComplexMap (CategoryStruct.comp f g) n = CategoryStruct.comp (R.cyclesShortComplexMap f n) (R'.cyclesShortComplexMap g n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L273-L280) · native range starts at 273.

<a id="api-caa0d46fce7557fc"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap_id`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap_id {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n : ℕ) : R.cyclesShortComplexMap (CategoryStruct.id R.cocomplex) n = CategoryStruct.id (R.cyclesShortComplex n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L268-L271) · native range starts at 268.

<a id="api-26b71f306e226698"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplexMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {X' A' : C} {R' : AcyclicResolution X' A'} (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) : R.cyclesShortComplex n ⟶ R'.cyclesShortComplex n
```

**Native source docstring:**

A cochain map induces a map of the canonical cycle short complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L256-L266) · native range starts at 256.

<a id="api-ec8d5dfacb24691b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.toCycles_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.toCycles_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℕ) [HomologicalComplex.HasHomology K (n + 1)] [HomologicalComplex.HasHomology L (n + 1)] {Z : C} (h : HomologicalComplex.cycles L (n + 1) ⟶ Z) : CategoryStruct.comp (f.f n) (CategoryStruct.comp (HomologicalComplex.toCycles L n (n + 1)) h) = CategoryStruct.comp (HomologicalComplex.toCycles K n (n + 1)) (CategoryStruct.comp (HomologicalComplex.cyclesMap f (n + 1)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L248-L248) · native range starts at 248.

<a id="api-f034f93005abdac2"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.toCycles_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.toCycles_naturality {C : Type u} [Category.{v, u} C] [Abelian C] {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℕ) [HomologicalComplex.HasHomology K (n + 1)] [HomologicalComplex.HasHomology L (n + 1)] : CategoryStruct.comp (f.f n) (HomologicalComplex.toCycles L n (n + 1)) = CategoryStruct.comp (HomologicalComplex.toCycles K n (n + 1)) (HomologicalComplex.cyclesMap f (n + 1))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L248-L254) · native range starts at 248.

<a id="api-32a17bd3f878dd3b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplex`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.cyclesShortComplex {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n : ℕ) : ShortComplex C
```

**Native source docstring:**

The canonical sequence from degree-`n` cycles through the degree-`n`
term to degree-`n+1` cycles.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L240-L245) · native range starts at 240.

<a id="api-d50987e362556c5a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extIsoCyclesZero_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extIsoCyclesZero_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (φ : R.Hom R' f) (q : ℕ) (x : Ext X A q) : (R'.extIsoCyclesZero q) (x.comp (mk₀ f) ⋯) = ((R.extIsoCyclesZero q) x).comp (mk₀ (HomologicalComplex.cyclesMap φ.hom 0)) ⋯
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L227-L238) · native range starts at 227.

<a id="api-442c8d54f851d593"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extIsoCyclesZero`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extIsoCyclesZero {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (q : ℕ) : Ext X A q ≃+ Ext X (HomologicalComplex.cycles R.cocomplex 0) q
```

**Native source docstring:**

Ext of the resolved object is transported to Ext of the degree-zero
cycles by the canonical augmentation isomorphism.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L221-L225) · native range starts at 221.

<a id="api-97ea0439b931ef0a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero_hom_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (φ : R.Hom R' f) {Z : C} (h : HomologicalComplex.cycles R'.cocomplex 0 ⟶ Z) : CategoryStruct.comp f (CategoryStruct.comp R'.objectIsoCyclesZero.hom h) = CategoryStruct.comp R.objectIsoCyclesZero.hom (CategoryStruct.comp (HomologicalComplex.cyclesMap φ.hom 0) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L206-L206) · native range starts at 206.

<a id="api-bf7b73a9dcb24f5f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero_hom_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (φ : R.Hom R' f) : CategoryStruct.comp f R'.objectIsoCyclesZero.hom = CategoryStruct.comp R.objectIsoCyclesZero.hom (HomologicalComplex.cyclesMap φ.hom 0)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L206-L219) · native range starts at 206.

<a id="api-64017665d4628602"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.objectIsoCyclesZero {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) : A ≅ HomologicalComplex.cycles R.cocomplex 0
```

**Native source docstring:**

The resolved object is canonically isomorphic to the degree-zero cycles
of an acyclic resolution.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L200-L204) · native range starts at 200.

<a id="api-cc372ae2ef231c9f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cocomplex_exactAt_succ`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cocomplex_exactAt_succ {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) (n : ℕ) : HomologicalComplex.ExactAt R.cocomplex (n + 1)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L194-L198) · native range starts at 194.

<a id="api-5d7bd1267bc65f4d"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_comp_hom_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_comp_hom_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} {R : AcyclicResolution X A} {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (φ : R.Hom R' f) {Z : CochainComplex C ℕ} (h : R'.cocomplex ⟶ Z) : CategoryStruct.comp R.ι (CategoryStruct.comp φ.hom h) = CategoryStruct.comp ((CochainComplex.single₀ C).map f) (CategoryStruct.comp R'.ι h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L185-L185) · native range starts at 185.

<a id="api-f2447551ab4ce650"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_comp_hom`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_comp_hom {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} {R : AcyclicResolution X A} {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (φ : R.Hom R' f) : CategoryStruct.comp R.ι φ.hom = CategoryStruct.comp ((CochainComplex.single₀ C).map f) R'.ι
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L185-L188) · native range starts at 185.

<a id="api-816c362e9024f817"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_f_zero_comp_hom_f_zero_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_f_zero_comp_hom_f_zero_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} {R : AcyclicResolution X A} {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (self : R.Hom R' f) {Z : C} (h : R'.cocomplex.X 0 ⟶ Z) : CategoryStruct.comp (R.ι.f 0) (CategoryStruct.comp (self.hom.f 0) h) = CategoryStruct.comp (((CochainComplex.single₀ C).map f).f 0) (CategoryStruct.comp (R'.ι.f 0) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L181-L181) · native range starts at 181.

<a id="api-a13fcef3b731c4d7"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_f_zero_comp_hom_f_zero`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.ι_f_zero_comp_hom_f_zero {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} {R : AcyclicResolution X A} {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (self : R.Hom R' f) : CategoryStruct.comp (R.ι.f 0) (self.hom.f 0) = CategoryStruct.comp (((CochainComplex.single₀ C).map f).f 0) (R'.ι.f 0)
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution.Hom`](#api-4e8f733b6051024b).

Native HTML text: `ι_f_zero_comp_hom_f_zero : CategoryStruct.comp (R.ι.f 0) (self.hom.f 0) = CategoryStruct.comp (((CochainComplex.single₀ C).map f).f 0) (R'.ι.f 0)`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L176-L176) · native range starts at 176.

<a id="api-5b0f49f0d85b51b0"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.hom`

```lean
abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.hom {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} {R : AcyclicResolution X A} {B : C} {R' : AcyclicResolution X B} {f : A ⟶ B} (self : R.Hom R' f) : R.cocomplex ⟶ R'.cocomplex
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution.Hom`](#api-4e8f733b6051024b).

Native HTML text: `hom : R.cocomplex ⟶ R'.cocomplex`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L175-L175) · native range starts at 175.

<a id="api-5c3f1bf56f9b559a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.mk`

```lean
constructor CategoryTheory.Abelian.Ext.AcyclicResolution.Hom.mk : {C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → [inst_1 : CategoryTheory.Abelian C] → [inst_2 : CategoryTheory.HasExt C] → {X A : C} → {R : CategoryTheory.Abelian.Ext.AcyclicResolution X A} → {B : C} → {R' : CategoryTheory.Abelian.Ext.AcyclicResolution X B} → {f : A ⟶ B} → (hom : R.cocomplex ⟶ R'.cocomplex) → CategoryTheory.CategoryStruct.comp (R.ι.f 0) (hom.f 0) = CategoryTheory.CategoryStruct.comp (((CochainComplex.single₀ C).map f).f 0) (R'.ι.f 0) → R.Hom R' f
```

**No native source docstring.** See the source and module guide.

**Native nested structure_fields display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution.Hom`](#api-4e8f733b6051024b).

Native HTML text: `hom : R.cocomplex ⟶ R'.cocomplexι_f_zero_comp_hom_f_zero : CategoryStruct.comp (R.ι.f 0) (self.hom.f 0) = CategoryStruct.comp (((CochainComplex.single₀ C).map f).f 0) (R'.ι.f 0)`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L173-L177) · native range starts at 173.

<a id="api-4e8f733b6051024b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.Hom`

```lean
structure CategoryTheory.Abelian.Ext.AcyclicResolution.Hom {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (R : AcyclicResolution X A) {B : C} (R' : AcyclicResolution X B) (f : A ⟶ B) : Type v
```

**Native source docstring:**

A map of acyclic resolutions above a map of resolved objects.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L173-L177) · native range starts at 173.

<a id="api-d3e80e79136e6969"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extAcyclic`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extAcyclic {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (self : AcyclicResolution X A) (n q : ℕ) : 0 < q → Subsingleton (Ext X (self.cocomplex.X n) q)
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `extAcyclic (n q : ℕ) : 0 < q → Subsingleton (Ext X (self.cocomplex.X n) q)`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L163-L163) · native range starts at 163.

<a id="api-8b841adc07b9d6d0"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.quasiIso`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.quasiIso {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (self : AcyclicResolution X A) : QuasiIso self.ι
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `quasiIso : QuasiIso self.ι`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L162-L162) · native range starts at 162.

<a id="api-d0706ce49a696167"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.ι`

```lean
abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.ι {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (self : AcyclicResolution X A) : (CochainComplex.single₀ C).obj A ⟶ self.cocomplex
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `ι : (CochainComplex.single₀ C).obj A ⟶ self.cocomplex`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L161-L161) · native range starts at 161.

<a id="api-e123f5f3678de050"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.hasHomology`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.hasHomology {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (self : AcyclicResolution X A) (n : ℕ) : HomologicalComplex.HasHomology self.cocomplex n
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `hasHomology (n : ℕ) : HomologicalComplex.HasHomology self.cocomplex n`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L160-L160) · native range starts at 160.

<a id="api-bc49d8769362f583"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cocomplex`

```lean
abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.cocomplex {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X A : C} (self : AcyclicResolution X A) : CochainComplex C ℕ
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `cocomplex : CochainComplex C ℕ`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L159-L159) · native range starts at 159.

<a id="api-0e1039e504cf7374"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.mk`

```lean
constructor CategoryTheory.Abelian.Ext.AcyclicResolution.mk : {C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → [inst_1 : CategoryTheory.Abelian C] → [inst_2 : CategoryTheory.HasExt C] → {X A : C} → (cocomplex : CochainComplex C ℕ) → [hasHomology : ∀ (n : ℕ), HomologicalComplex.HasHomology cocomplex n] → (ι : (CochainComplex.single₀ C).obj A ⟶ cocomplex) → autoParam (QuasiIso ι) CategoryTheory.Abelian.Ext.AcyclicResolution.quasiIso._autoParam → (∀ (n q : ℕ), 0 < q → Subsingleton (CategoryTheory.Abelian.Ext X (cocomplex.X n) q)) → CategoryTheory.Abelian.Ext.AcyclicResolution X A
```

**No native source docstring.** See the source and module guide.

**Native nested structure_fields display site** of [`CategoryTheory.Abelian.Ext.AcyclicResolution`](#api-06e926e408c3bded).

Native HTML text: `cocomplex : CochainComplex C ℕhasHomology (n : ℕ) : HomologicalComplex.HasHomology self.cocomplex nι : (CochainComplex.single₀ C).obj A ⟶ self.cocomplexquasiIso : QuasiIso self.ιextAcyclic (n q : ℕ) : 0 < q → Subsingleton (Ext X (self.cocomplex.X n) q)`

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L156-L163) · native range starts at 156.

<a id="api-06e926e408c3bded"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution`

```lean
structure CategoryTheory.Abelian.Ext.AcyclicResolution {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] (X A : C) : Type (max u v)
```

**Native source docstring:**

A nonnegative resolution whose terms are acyclic for `Ext X -` in
positive degrees.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L156-L163) · native range starts at 156.

<a id="api-af7a22bd50ccbe54"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelIso_inv_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.covariantCokernelIso_inv_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] {Z : AddCommGrpCat} (h : Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S₂.g).postcomp X ⋯)) ⟶ Z) : CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X ⋯)) (CategoryStruct.comp (covariantCokernelIso h₂ X).inv h) = CategoryStruct.comp (covariantCokernelIso h₁ X).inv (CategoryStruct.comp (covariantCokernelMap f X) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L143-L143) · native range starts at 143.

<a id="api-31a1498dbca168f5"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelIso_inv_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.covariantCokernelIso_inv_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] : CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X ⋯)) (covariantCokernelIso h₂ X).inv = CategoryStruct.comp (covariantCokernelIso h₁ X).inv (covariantCokernelMap f X)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L143-L154) · native range starts at 143.

<a id="api-923e9d186b39eb2d"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelIso_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.covariantCokernelIso_hom_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] {Z : AddCommGrpCat} (h : ↧(Ext X S₂.X₁ 1) ⟶ Z) : CategoryStruct.comp (covariantCokernelMap f X) (CategoryStruct.comp (covariantCokernelIso h₂ X).hom h) = CategoryStruct.comp (covariantCokernelIso h₁ X).hom (CategoryStruct.comp (AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X ⋯)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L126-L126) · native range starts at 126.

<a id="api-2e633e9672f7738f"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelIso_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.covariantCokernelIso_hom_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) [Subsingleton (Ext X S₁.X₂ 1)] [Subsingleton (Ext X S₂.X₂ 1)] : CategoryStruct.comp (covariantCokernelMap f X) (covariantCokernelIso h₂ X).hom = CategoryStruct.comp (covariantCokernelIso h₁ X).hom (AddCommGrpCat.ofHom ((mk₀ f.τ₁).postcomp X ⋯))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L126-L141) · native range starts at 126.

<a id="api-f7cb85db92593709"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.covariantCokernelMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) (X : C) : Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S₁.g).postcomp X ⋯)) ⟶ Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S₂.g).postcomp X ⋯))
```

**Native source docstring:**

The map of the degree-zero cokernels induced by a map of short
complexes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L107-L124) · native range starts at 107.

<a id="api-da83d7af238bbc1e"></a>

### `CategoryTheory.Abelian.Ext.cokernelπ_covariantCokernelIso_hom_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.cokernelπ_covariantCokernelIso_hom_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (X : C) [Subsingleton (Ext X S.X₂ 1)] {Z : AddCommGrpCat} (h : ↧(Ext X S.X₁ 1) ⟶ Z) : CategoryStruct.comp (Limits.cokernel.π (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X ⋯))) (CategoryStruct.comp (covariantCokernelIso hS X).hom h) = CategoryStruct.comp (AddCommGrpCat.ofHom (hS.extClass.postcomp X ⋯)) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L96-L96) · native range starts at 96.

<a id="api-8c81dbaffbd0a57f"></a>

### `CategoryTheory.Abelian.Ext.cokernelπ_covariantCokernelIso_hom`

```lean
theorem CategoryTheory.Abelian.Ext.cokernelπ_covariantCokernelIso_hom {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (X : C) [Subsingleton (Ext X S.X₂ 1)] : CategoryStruct.comp (Limits.cokernel.π (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X ⋯))) (covariantCokernelIso hS X).hom = AddCommGrpCat.ofHom (hS.extClass.postcomp X ⋯)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L96-L105) · native range starts at 96.

<a id="api-70a7def18259b050"></a>

### `CategoryTheory.Abelian.Ext.covariantCokernelIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.covariantCokernelIso {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (X : C) [Subsingleton (Ext X S.X₂ 1)] : Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X ⋯)) ≅ ↧(Ext X S.X₁ 1)
```

**Native source docstring:**

Degree-one Ext is the cokernel of the degree-zero map in a short exact
sequence when degree-one Ext of the middle object vanishes.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L65-L94) · native range starts at 65.

<a id="api-ece202cc1ec12692"></a>

### `CategoryTheory.Abelian.Ext.covariantDimensionShift_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.covariantDimensionShift_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) (X : C) (n : ℕ) (x : Ext X S₁.X₃ n) : (x.comp (mk₀ f.τ₃) ⋯).comp h₂.extClass ⋯ = (x.comp h₁.extClass ⋯).comp (mk₀ f.τ₁) ⋯
```

**Native source docstring:**

The covariant connecting map defined by an extension class is natural in
maps of short exact sequences.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L54-L63) · native range starts at 54.

<a id="api-b34540cec45bd5eb"></a>

### `CategoryTheory.Abelian.Ext.covariantDimensionShift`

```lean
noncomputable def CategoryTheory.Abelian.Ext.covariantDimensionShift {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (X : C) (n : ℕ) [Subsingleton (Ext X S.X₂ n)] [Subsingleton (Ext X S.X₂ (n + 1))] : Ext X S.X₃ n ≃+ Ext X S.X₁ (n + 1)
```

**Native source docstring:**

The covariant dimension-shift equivalence attached to a short exact
sequence when the middle object has vanishing Ext in both adjacent degrees.

[Frozen source](../SheafCohomology/AcyclicResolution.lean#L29-L52) · native range starts at 29.

## `SheafCohomology.ColimitPostApp`

Scope: subject module.

<a id="api-7976cf42b4d42c3b"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.colimit_post_app_isIso_of_preserves`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.colimit_post_app_isIso_of_preserves {J : Type uJ} [CategoryTheory.Category.{vJ, uJ} J] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] {K : Type uK} [CategoryTheory.Category.{vK, uK} K] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] (F : CategoryTheory.Functor J C) (L : CategoryTheory.Functor C (CategoryTheory.Functor K D)) (k : K) [CategoryTheory.Limits.HasColimit F] [CategoryTheory.Limits.HasColimitsOfShape J D] [CategoryTheory.Limits.PreservesColimit F (L.comp ((CategoryTheory.evaluation K D).obj k))] : CategoryTheory.IsIso ((CategoryTheory.Limits.colimit.post F L).app k)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/ColimitPostApp.lean#L53-L59) · native range starts at 53.

<a id="api-71faaf97c1259205"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.colimit_post_app_eq`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.colimit_post_app_eq {J : Type uJ} [CategoryTheory.Category.{vJ, uJ} J] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] {K : Type uK} [CategoryTheory.Category.{vK, uK} K] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] (F : CategoryTheory.Functor J C) (L : CategoryTheory.Functor C (CategoryTheory.Functor K D)) (k : K) [CategoryTheory.Limits.HasColimit F] [CategoryTheory.Limits.HasColimitsOfShape J D] : (CategoryTheory.Limits.colimit.post F L).app k = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (F.comp L) k).hom (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.HasColimit.isoOfNatIso (F.associator L ((CategoryTheory.evaluation K D).obj k))).hom (CategoryTheory.Limits.colimit.post F (L.comp ((CategoryTheory.evaluation K D).obj k))))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/ColimitPostApp.lean#L36-L51) · native range starts at 36.

## `SheafCohomology.ColimitTransport`

Scope: subject module.

<a id="api-9c654e3bcbcf6219"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.colimMap_whiskerLeft_comp_colimit_post`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.colimMap_whiskerLeft_comp_colimit_post {J : Type uJ} [CategoryTheory.Category.{vJ, uJ} J] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] (F : CategoryTheory.Functor J C) (L R : CategoryTheory.Functor C D) (α : L ⟶ R) [CategoryTheory.Limits.HasColimit F] [CategoryTheory.Limits.HasColimit (F.comp L)] [CategoryTheory.Limits.HasColimit (F.comp R)] : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft α)) (CategoryTheory.Limits.colimit.post F R) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F L) (α.app (CategoryTheory.Limits.colimit F))
```

**Native source docstring:**

The canonical colimit comparison commutes with change of the target
functor by a natural transformation.

[Frozen source](../SheafCohomology/ColimitTransport.lean#L32-L43) · native range starts at 32.

## `SheafCohomology.CompactOpenSections`

Scope: subject module.

<a id="api-1d1b336fd67f803d"></a>

### `SheafCohomology.CompactOpenSections.preservesColimit_globalSections`

```lean
theorem SheafCohomology.CompactOpenSections.preservesColimit_globalSections {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] : CategoryTheory.Limits.PreservesColimit F (sectionsOf ⊤)
```

**Native source docstring:**

Global sections preserve a filtered colimit on a quasi-compact,
prespectral, quasi-separated space.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L794-L800) · native range starts at 794.

<a id="api-de9b6fbaf8610821"></a>

### `SheafCohomology.CompactOpenSections.preservesColimit_sections`

```lean
theorem SheafCohomology.CompactOpenSections.preservesColimit_sections {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [PrespectralSpace X] [QuasiSeparatedSpace X] (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.Limits.PreservesColimit F (sectionsOf U)
```

**Native source docstring:**

Evaluation on a compact open preserves a filtered colimit of sheaves.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L783-L790) · native range starts at 783.

<a id="api-ce19cf196857f069"></a>

### `SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso`

```lean
theorem SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [PrespectralSpace X] [QuasiSeparatedSpace X] (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.IsIso (CategoryTheory.Limits.colimit.post F (sectionsOf U))
```

**Native source docstring:**

The canonical colimit comparison for sections on a compact open is an
isomorphism.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L756-L779) · native range starts at 756.

<a id="api-ec4282052b1dd39a"></a>

### `SheafCohomology.CompactOpenSections.explicitSectionsComparison_isIso`

```lean
theorem SheafCohomology.CompactOpenSections.explicitSectionsComparison_isIso {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [PrespectralSpace X] [QuasiSeparatedSpace X] (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.IsIso (explicitSectionsComparison F U)
```

**Native source docstring:**

The direct comparison is an isomorphism on a compact open of a
prespectral, quasi-separated space.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L744-L752) · native range starts at 744.

<a id="api-80013e7e654d2180"></a>

### `SheafCohomology.CompactOpenSections.explicitSectionsComparison_surjective`

```lean
theorem SheafCohomology.CompactOpenSections.explicitSectionsComparison_surjective {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [PrespectralSpace X] [QuasiSeparatedSpace X] (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F U))
```

**Native source docstring:**

The direct comparison is surjective on a compact open of a prespectral,
quasi-separated space.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L535-L740) · native range starts at 535.

<a id="api-31d32f1f073656dc"></a>

### `SheafCohomology.CompactOpenSections.exists_compact_open_local_preimage`

```lean
theorem SheafCohomology.CompactOpenSections.exists_compact_open_local_preimage {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [PrespectralSpace X] (U : TopologicalSpace.Opens X) (s : CategoryTheory.ToType ((CategoryTheory.sheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).obj (Opposite.op U))) (x : X) (hx : x ∈ U) : ∃ (V : TopologicalSpace.Opens X) (f : V ⟶ U), x ∈ V ∧ IsCompact ↑V ∧ ∃ (t : CategoryTheory.ToType (CategoryTheory.Limits.colimit (F.comp (sectionsOf V)))), (CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F V)) t = (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.sheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).map f.op)) s
```

**Native source docstring:**

Every section of the explicit sheaf colimit is locally represented by a
section-colimit element on a compact open neighborhood.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L492-L532) · native range starts at 492.

<a id="api-5c28ddbb4d819eb8"></a>

### `SheafCohomology.CompactOpenSections.explicitSectionsComparison_injective`

```lean
theorem SheafCohomology.CompactOpenSections.explicitSectionsComparison_injective {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F U))
```

**Native source docstring:**

The direct comparison is injective on a compact open.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L385-L485) · native range starts at 385.

<a id="api-ace918fbffb16a20"></a>

### `SheafCohomology.CompactOpenSections.exists_open_restriction_eq_of_explicitComparison_eq`

```lean
theorem SheafCohomology.CompactOpenSections.exists_open_restriction_eq_of_explicitComparison_eq {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) {s t : CategoryTheory.ToType (CategoryTheory.Limits.colimit (F.comp (sectionsOf U)))} (h : (CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F U)) s = (CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F U)) t) (x : X) (hx : x ∈ U) : ∃ (V : TopologicalSpace.Opens X) (f : V ⟶ U), x ∈ V ∧ (CategoryTheory.ConcreteCategory.hom ((underlyingPresheafColimit F).map f.op)) (explicitPresheafSectionRepresentative F U s) = (CategoryTheory.ConcreteCategory.hom ((underlyingPresheafColimit F).map f.op)) (explicitPresheafSectionRepresentative F U t)
```

**Native source docstring:**

Equality after sheafification is witnessed on an open neighborhood of
each point.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L357-L382) · native range starts at 357.

<a id="api-3c254e7b6dc4f0df"></a>

### `SheafCohomology.CompactOpenSections.exists_stage_of_section_restriction_eq`

```lean
theorem SheafCohomology.CompactOpenSections.exists_stage_of_section_restriction_eq {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) (s t : CategoryTheory.ToType ((F.obj i).obj.obj (Opposite.op U))) {V : TopologicalSpace.Opens X} (f : V ⟶ U) (h : (CategoryTheory.ConcreteCategory.hom ((underlyingPresheafColimit F).map f.op)) (explicitPresheafSectionRepresentative F U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf U)) i)) s)) = (CategoryTheory.ConcreteCategory.hom ((underlyingPresheafColimit F).map f.op)) (explicitPresheafSectionRepresentative F U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf U)) i)) t))) : ∃ (k : I) (g : i ⟶ k), (CategoryTheory.ConcreteCategory.hom ((F.comp (sectionsOf V)).map g)) ((CategoryTheory.ConcreteCategory.hom ((F.obj i).obj.map f.op)) s) = (CategoryTheory.ConcreteCategory.hom ((F.comp (sectionsOf V)).map g)) ((CategoryTheory.ConcreteCategory.hom ((F.obj i).obj.map f.op)) t)
```

**Native source docstring:**

Equality of two restrictions in the pointwise colimit is witnessed at one
later stage.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L325-L350) · native range starts at 325.

<a id="api-1e36f7010897e297"></a>

### `SheafCohomology.CompactOpenSections.underlyingPresheafColimit_map_representative_ι`

```lean
theorem SheafCohomology.CompactOpenSections.underlyingPresheafColimit_map_representative_ι {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) (s : CategoryTheory.ToType ((F.obj i).obj.obj (Opposite.op U))) {V : TopologicalSpace.Opens X} (f : V ⟶ U) : (CategoryTheory.ConcreteCategory.hom ((underlyingPresheafColimit F).map f.op)) (explicitPresheafSectionRepresentative F U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf U)) i)) s)) = (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Limits.colimit.ι (F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)) i).app (Opposite.op V))) ((CategoryTheory.ConcreteCategory.hom ((F.obj i).obj.map f.op)) s)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L300-L316) · native range starts at 300.

<a id="api-95800dd6094e5e1d"></a>

### `SheafCohomology.CompactOpenSections.explicitPresheafSectionRepresentative_ι`

```lean
theorem SheafCohomology.CompactOpenSections.explicitPresheafSectionRepresentative_ι {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) (s : CategoryTheory.ToType ((F.obj i).obj.obj (Opposite.op U))) : explicitPresheafSectionRepresentative F U ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf U)) i)) s) = (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.Limits.colimit.ι (F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)) i).app (Opposite.op U))) s
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L274-L290) · native range starts at 274.

<a id="api-8dca6f4592522089"></a>

### `SheafCohomology.CompactOpenSections.explicitPresheafSectionRepresentative`

```lean
noncomputable def SheafCohomology.CompactOpenSections.explicitPresheafSectionRepresentative {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (s : CategoryTheory.ToType (CategoryTheory.Limits.colimit (F.comp (sectionsOf U)))) : CategoryTheory.ToType ((underlyingPresheafColimit F).obj (Opposite.op U))
```

**Native source docstring:**

A section-colimit element viewed in the pointwise presheaf colimit.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L258-L264) · native range starts at 258.

<a id="api-e2528210b3e78a36"></a>

### `SheafCohomology.CompactOpenSections.explicitSectionsComparison_ι_naturality`

```lean
theorem SheafCohomology.CompactOpenSections.explicitSectionsComparison_ι_naturality {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) {V U : TopologicalSpace.Opens X} (f : V ⟶ U) (i : I) (s : CategoryTheory.ToType ((F.obj i).obj.obj (Opposite.op U))) : (CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F V)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf V)) i)) ((CategoryTheory.ConcreteCategory.hom ((F.obj i).obj.map f.op)) s)) = (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.sheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).map f.op)) ((CategoryTheory.ConcreteCategory.hom (explicitSectionsComparison F U)) ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.colimit.ι (F.comp (sectionsOf U)) i)) s))
```

**Native source docstring:**

Naturality of the direct comparison with respect to restriction of
sections.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L209-L256) · native range starts at 209.

<a id="api-5cfd9fedb9ec40d4"></a>

### `SheafCohomology.CompactOpenSections.transportedExplicitSectionsComparison_eq`

```lean
theorem SheafCohomology.CompactOpenSections.transportedExplicitSectionsComparison_eq {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) : transportedExplicitSectionsComparison F U = CategoryTheory.Limits.colimit.post F (sectionsOf U)
```

**Native source docstring:**

The transported direct comparison is the canonical `colimit.post`
comparison.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L175-L200) · native range starts at 175.

<a id="api-37cfe42ac4e796e8"></a>

### `SheafCohomology.CompactOpenSections.explicitSheafColimitCocone_ι_iso_hom_app`

```lean
theorem SheafCohomology.CompactOpenSections.explicitSheafColimitCocone_ι_iso_hom_app {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) : CategoryTheory.CategoryStruct.comp (((explicitSheafColimitCocone F).ι.app i).hom.app (Opposite.op U)) ((explicitSheafColimitIso F).hom.hom.app (Opposite.op U)) = (CategoryTheory.Limits.colimit.ι F i).hom.app (Opposite.op U)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L159-L166) · native range starts at 159.

<a id="api-83bfa5a9f766710c"></a>

### `SheafCohomology.CompactOpenSections.colimit_ι_explicitSectionsComparison_assoc`

```lean
theorem SheafCohomology.CompactOpenSections.colimit_ι_explicitSectionsComparison_assoc {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) {Z : C} (h : (CategoryTheory.sheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).obj (Opposite.op U) ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι ((F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ C).obj (Opposite.op U))) i) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)) (Opposite.op U)).inv (CategoryTheory.CategoryStruct.comp ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).app (Opposite.op U)) h)) = CategoryTheory.CategoryStruct.comp (((explicitSheafColimitCocone F).ι.app i).hom.app (Opposite.op U)) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L135-L135) · native range starts at 135.

<a id="api-df01aa42da5fbc87"></a>

### `SheafCohomology.CompactOpenSections.colimit_ι_explicitSectionsComparison`

```lean
theorem SheafCohomology.CompactOpenSections.colimit_ι_explicitSectionsComparison {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) (i : I) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι ((F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ C).obj (Opposite.op U))) i) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (F.comp (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) C)) (Opposite.op U)).inv ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).app (Opposite.op U))) = ((explicitSheafColimitCocone F).ι.app i).hom.app (Opposite.op U)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L135-L153) · native range starts at 135.

<a id="api-8e1e153f6836406c"></a>

### `SheafCohomology.CompactOpenSections.transportedExplicitSectionsComparison`

```lean
noncomputable def SheafCohomology.CompactOpenSections.transportedExplicitSectionsComparison {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) : CategoryTheory.Limits.colimit (F.comp (sectionsOf U)) ⟶ (sectionsOf U).obj (CategoryTheory.Limits.colimit F)
```

**Native source docstring:**

The direct comparison transported to the chosen sheaf colimit.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L125-L129) · native range starts at 125.

<a id="api-b6ac58fbc293e45e"></a>

### `SheafCohomology.CompactOpenSections.explicitSectionsComparison`

```lean
noncomputable def SheafCohomology.CompactOpenSections.explicitSectionsComparison {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) : CategoryTheory.Limits.colimit (F.comp (sectionsOf U)) ⟶ (CategoryTheory.sheafify (Opens.grothendieckTopology X) (underlyingPresheafColimit F)).obj (Opposite.op U)
```

**Native source docstring:**

The direct comparison from the colimit of sections to sections of the
explicit sheafification model.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L113-L123) · native range starts at 113.

<a id="api-ff879aae6d93d1ac"></a>

### `SheafCohomology.CompactOpenSections.explicitSheafColimitIso`

```lean
noncomputable def SheafCohomology.CompactOpenSections.explicitSheafColimitIso {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C).obj (underlyingPresheafColimit F) ≅ CategoryTheory.Limits.colimit F
```

**Native source docstring:**

The unique isomorphism from the explicit sheafification model to the
chosen sheaf colimit.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L105-L111) · native range starts at 105.

<a id="api-56bc9470c152f9b3"></a>

### `SheafCohomology.CompactOpenSections.explicitSheafColimitCoconeIsColimit`

```lean
noncomputable def SheafCohomology.CompactOpenSections.explicitSheafColimitCoconeIsColimit {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) : CategoryTheory.Limits.IsColimit (explicitSheafColimitCocone F)
```

**Native source docstring:**

The explicit sheafification cocone is colimiting.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L94-L103) · native range starts at 94.

<a id="api-1d07c3a03be4723b"></a>

### `SheafCohomology.CompactOpenSections.explicitSheafColimitCocone`

```lean
noncomputable abbrev SheafCohomology.CompactOpenSections.explicitSheafColimitCocone {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) : CategoryTheory.Limits.Cocone F
```

**Native source docstring:**

The sheafification cocone built from the pointwise presheaf colimit.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L87-L92) · native range starts at 87.

<a id="api-4b1bced0bc85e77c"></a>

### `SheafCohomology.CompactOpenSections.underlyingPresheafColimit`

```lean
noncomputable abbrev SheafCohomology.CompactOpenSections.underlyingPresheafColimit {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) : CategoryTheory.Functor (TopologicalSpace.Opens X)ᵒᵖ C
```

**Native source docstring:**

The pointwise presheaf colimit underlying the explicit sheaf colimit.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L81-L85) · native range starts at 81.

<a id="api-36facce8c31f62d6"></a>

### `SheafCohomology.CompactOpenSections.sections`

```lean
abbrev SheafCohomology.CompactOpenSections.sections {X : Type u} [TopologicalSpace X] (U : TopologicalSpace.Opens X) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) AddCommGrpCat
```

**Native source docstring:**

Evaluation of an `AddCommGrpCat`-valued sheaf on an open set.

This retains the original additive API while `sectionsOf` supplies the generic
concrete-category evaluator used by the filtered-colimit proof.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L61-L68) · native range starts at 61.

<a id="api-00f822e55578a28b"></a>

### `SheafCohomology.CompactOpenSections.sectionsOf`

```lean
abbrev SheafCohomology.CompactOpenSections.sectionsOf {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] (U : TopologicalSpace.Opens X) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) C
```

**Native source docstring:**

Evaluation of a `C`-valued sheaf on an open set.

[Frozen source](../SheafCohomology/CompactOpenSections.lean#L54-L59) · native range starts at 54.

## `SheafCohomology.DegreeZero`

Scope: subject module.

<a id="api-df258b9dcd8e0745"></a>

### `SheafCohomology.DegreeZero.preservesColimit_functorH_zero`

```lean
theorem SheafCohomology.DegreeZero.preservesColimit_functorH_zero {X : Type u} [TopologicalSpace X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] [UnivLE.{u, v}] [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)) [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] : CategoryTheory.Limits.PreservesColimit F (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0)
```

**Native source docstring:**

On a compact prespectral quasi-separated space, degree-zero sheaf
cohomology preserves same-size filtered colimits.

[Frozen source](../SheafCohomology/DegreeZero.lean#L59-L67) · native range starts at 59.

<a id="api-a9eacb0cae1f101f"></a>

### `SheafCohomology.DegreeZero.functorHZeroIsoSections`

```lean
noncomputable def SheafCohomology.DegreeZero.functorHZeroIsoSections {X : Type u} [TopologicalSpace X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] : CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0 ≅ CompactOpenSections.sections ⊤
```

**Native source docstring:**

Degree-zero sheaf cohomology is naturally isomorphic to sections on the
terminal open.

[Frozen source](../SheafCohomology/DegreeZero.lean#L38-L50) · native range starts at 38.

## `SheafCohomology.FilteredColimitFunctorH`

Scope: subject module.

<a id="api-6486dd66ffd4a851"></a>

### `TopCat.Sheaf.preservesColimit_functorH`

```lean
theorem TopCat.Sheaf.preservesColimit_functorH {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) : CategoryTheory.Limits.PreservesColimit F (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q)
```

**Native source docstring:**

Sheaf cohomology in every degree preserves same-size filtered colimits on
a compact prespectral quasi-separated space.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L794-L803) · native range starts at 794.

<a id="api-9c8a1b1e4d90206d"></a>

### `TopCat.Sheaf.preservesColimit_functorH_positive`

```lean
theorem TopCat.Sheaf.preservesColimit_functorH_positive {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : CategoryTheory.Limits.PreservesColimit F (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q)
```

**Native source docstring:**

Positive-degree sheaf cohomology preserves same-size filtered colimits on
a compact prespectral quasi-separated space.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L780-L792) · native range starts at 780.

<a id="api-c1d0ee929484a377"></a>

### `TopCat.Sheaf.filteredFlasquePositiveColimitIso_hom`

```lean
theorem TopCat.Sheaf.filteredFlasquePositiveColimitIso_hom {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : (filteredFlasquePositiveColimitIso F q hq).hom = CategoryTheory.Limits.colimit.post F (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q)
```

**Native source docstring:**

The constructed positive-degree isomorphism is the canonical comparison
map from the colimit of the values to the value on the colimit.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L720-L778) · native range starts at 720.

<a id="api-9d3d789dd8295cdc"></a>

### `TopCat.Sheaf.colimitι_comp_ofFunctorColimIso_inv_comp_sectionsIso_hom`

```lean
theorem TopCat.Sheaf.colimitι_comp_ofFunctorColimIso_inv_comp_sectionsIso_hom {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] (i : I) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (filteredFlasqueResolutionSectionsDiagram F) i) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.ofFunctorColimIso (filteredFlasqueResolutionSectionsDiagram F)).inv (filteredFlasqueResolutionSectionsIso F).hom) = ((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map (filteredFlasqueResolutionι F i)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L698-L717) · native range starts at 698.

<a id="api-52e9244d29840b7b"></a>

### `TopCat.Sheaf.ofFunctorColimitι_comp_filteredFlasqueResolutionSectionsIso_hom`

```lean
theorem TopCat.Sheaf.ofFunctorColimitι_comp_filteredFlasqueResolutionSectionsIso_hom {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] (i : I) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.ofFunctorColimitι (filteredFlasqueResolutionSectionsDiagram F) i) (filteredFlasqueResolutionSectionsIso F).hom = ((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map (filteredFlasqueResolutionι F i)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L668-L693) · native range starts at 668.

<a id="api-ce147bb4c4316226"></a>

### `TopCat.Sheaf.filteredFlasquePositiveColimitIso`

```lean
noncomputable def TopCat.Sheaf.filteredFlasquePositiveColimitIso {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : CategoryTheory.Limits.colim.obj (F.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q)) ≅ (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q).obj (CategoryTheory.Limits.colim.obj F)
```

**Native source docstring:**

The positive-degree comparison from the colimit of stagewise cohomology
to the cohomology of the colimit sheaf.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L650-L663) · native range starts at 650.

<a id="api-3141c26c6eecf758"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionSectionsIso`

```lean
noncomputable abbrev TopCat.Sheaf.filteredFlasqueResolutionSectionsIso {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] : (CategoryTheory.Limits.colim.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((((CategoryTheory.Functor.whiskeringRight I (Sheaf AddCommGrpCat X) AddCommGrpCat).obj (SheafCohomology.CompactOpenSections.sections ⊤)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F)) ≅ ((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CategoryTheory.Limits.colim.mapHomologicalComplex (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F))
```

**Native source docstring:**

Terminal sections commute with the degreewise filtered colimit of the
stagewise flasque resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L638-L648) · native range starts at 638.

<a id="api-4775ad21ab8c29aa"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionTerm_preservesColimit_sections`

```lean
instance TopCat.Sheaf.filteredFlasqueResolutionTerm_preservesColimit_sections {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] (n : ℕ) : CategoryTheory.Limits.PreservesColimit ((filteredFlasqueResolutionComplexDiagram F).X n) (SheafCohomology.CompactOpenSections.sections ⊤)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L631-L636) · native range starts at 631.

<a id="api-4b79ac9172b15ff3"></a>

### `TopCat.Sheaf.filteredFlasqueResolution_sections_additive`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolution_sections_additive {X : TopCat} : (SheafCohomology.CompactOpenSections.sections ⊤).Additive
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L623-L629) · native range starts at 623.

<a id="api-29d8d2370c6daddb"></a>

### `TopCat.Sheaf.filteredFlasquePositiveIsoSectionsHomologyDiagram`

```lean
noncomputable def TopCat.Sheaf.filteredFlasquePositiveIsoSectionsHomologyDiagram {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : F.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) q) ≅ (filteredFlasqueResolutionSectionsDiagram F).comp (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) q)
```

**Native source docstring:**

The positive-degree stagewise cohomology comparisons, assembled as a
natural isomorphism of filtered diagrams.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L606-L621) · native range starts at 606.

<a id="api-cfe09b77b436d751"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionSectionsDiagram`

```lean
noncomputable abbrev TopCat.Sheaf.filteredFlasqueResolutionSectionsDiagram {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : CategoryTheory.Functor I (CochainComplex AddCommGrpCat ℕ)
```

**Native source docstring:**

The terminal-sections complexes of the stagewise functorial flasque
resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L598-L604) · native range starts at 598.

<a id="api-cddd7e366b29837e"></a>

### `TopCat.Sheaf.filteredFlasqueAcyclicResolutionHom`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueAcyclicResolutionHom {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (i : I) : (F.obj i).flasqueAcyclicResolution.Hom (filteredFlasqueAcyclicResolution F) (CategoryTheory.Limits.colimit.ι F i)
```

**Native source docstring:**

The canonical stage map, packaged as a map from the stagewise acyclic
resolution to the filtered-colimit acyclic resolution.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L586-L596) · native range starts at 586.

<a id="api-3be904c30b2d7f89"></a>

### `TopCat.Sheaf.filteredFlasqueResolution_stage_assoc`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolution_stage_assoc {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) {Z : CochainComplex (Sheaf AddCommGrpCat X) ℕ} (h : filteredFlasqueResolution F ⟶ Z) : CategoryTheory.CategoryStruct.comp ((CochainComplex.single₀ (Sheaf AddCommGrpCat X)).map (CategoryTheory.Limits.colimit.ι F i)) (CategoryTheory.CategoryStruct.comp (filteredFlasqueResolutionAugmentation F) h) = CategoryTheory.CategoryStruct.comp (F.obj i).toFlasqueResolution (CategoryTheory.CategoryStruct.comp (filteredFlasqueResolutionι F i) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L575-L575) · native range starts at 575.

<a id="api-4478b8966cb90b4c"></a>

### `TopCat.Sheaf.filteredFlasqueResolution_stage`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolution_stage {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) : CategoryTheory.CategoryStruct.comp ((CochainComplex.single₀ (Sheaf AddCommGrpCat X)).map (CategoryTheory.Limits.colimit.ι F i)) (filteredFlasqueResolutionAugmentation F) = CategoryTheory.CategoryStruct.comp (F.obj i).toFlasqueResolution (filteredFlasqueResolutionι F i)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L575-L584) · native range starts at 575.

<a id="api-671e64a44b919184"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionι`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueResolutionι {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) : (F.obj i).flasqueResolution ⟶ filteredFlasqueResolution F
```

**Native source docstring:**

The canonical map from a stage's flasque resolution to the degreewise
filtered colimit resolution.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L564-L569) · native range starts at 564.

<a id="api-3e55d0c400684531"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionComplexColimitι`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueResolutionComplexColimitι {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) : (((CategoryTheory.evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F) ⟶ filteredFlasqueResolution F
```

**Native source docstring:**

The canonical map from one stage's complex to the degreewise filtered
colimit complex.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L554-L562) · native range starts at 554.

<a id="api-fb245f4d31c6c247"></a>

### `TopCat.Sheaf.filteredFlasqueAcyclicResolution`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueAcyclicResolution {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] : CategoryTheory.Abelian.Ext.AcyclicResolution ((CategoryTheory.constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) (CategoryTheory.Limits.colim.obj F)
```

**Native source docstring:**

The degreewise filtered-colimit resolution, packaged as a resolution
acyclic for the Ext functor defining sheaf cohomology.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L537-L552) · native range starts at 537.

<a id="api-6123cbace59b94d4"></a>

### `TopCat.Sheaf.filteredFlasqueResolution_isQuasiFlasque`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolution_isQuasiFlasque {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] (n : ℕ) : IsQuasiFlasque ((filteredFlasqueResolution F).X n)
```

**Native source docstring:**

Every term of the filtered-colimit resolution is quasi-flasque.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L522-L531) · native range starts at 522.

<a id="api-d49e092c3c816506"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionAugmentation_quasiIso`

```lean
instance TopCat.Sheaf.filteredFlasqueResolutionAugmentation_quasiIso {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : QuasiIso (filteredFlasqueResolutionAugmentation F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L517-L520) · native range starts at 517.

<a id="api-e814e608297f7cd9"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionAugmentation`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueResolutionAugmentation {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).obj (CategoryTheory.Limits.colimit F) ⟶ filteredFlasqueResolution F
```

**Native source docstring:**

The augmentation from the colimit sheaf to the degreewise colimit of the
stagewise flasque resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L505-L515) · native range starts at 505.

<a id="api-d3b2acbd7eaf9d8b"></a>

### `TopCat.Sheaf.filteredFlasqueResolution`

```lean
noncomputable abbrev TopCat.Sheaf.filteredFlasqueResolution {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : CochainComplex (Sheaf AddCommGrpCat X) ℕ
```

**Native source docstring:**

The degreewise filtered colimit of the functorial flasque resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L499-L503) · native range starts at 499.

<a id="api-3bdf9b8280847501"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_quasiIso`

```lean
instance TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_quasiIso {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : QuasiIso (filteredFlasqueResolutionDiagramAugmentation F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L492-L497) · native range starts at 492.

<a id="api-f4d7d35d3e9adb6c"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_evaluation`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_evaluation {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) : (((CategoryTheory.evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex (ComplexShape.up ℕ)).map (filteredFlasqueResolutionDiagramAugmentation F) = CategoryTheory.CategoryStruct.comp ((HomologicalComplex.singleMapHomologicalComplex ((CategoryTheory.evaluation I (Sheaf AddCommGrpCat X)).obj i) (ComplexShape.up ℕ) 0).hom.app F) (CategoryTheory.CategoryStruct.comp (F.obj i).toFlasqueResolution (filteredFlasqueResolutionComplexDiagramEvalIso F i).inv)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L473-L490) · native range starts at 473.

<a id="api-04dd816973b35aca"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionComplexDiagramEvalIso_inv_f`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolutionComplexDiagramEvalIso_inv_f {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) (n : ℕ) : (filteredFlasqueResolutionComplexDiagramEvalIso F i).inv.f n = CategoryTheory.CategoryStruct.id ((F.obj i).flasqueResolution.X n)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L466-L470) · native range starts at 466.

<a id="api-0e1b5f1bd6550336"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionComplexDiagramEvalIso`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueResolutionComplexDiagramEvalIso {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) (i : I) : (((CategoryTheory.evaluation I (Sheaf AddCommGrpCat X)).obj i).mapHomologicalComplex (ComplexShape.up ℕ)).obj (filteredFlasqueResolutionComplexDiagram F) ≅ (F.obj i).flasqueResolution
```

**Native source docstring:**

Evaluation of the complex of diagrams at a stage agrees with that stage's
functorial flasque resolution.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L456-L463) · native range starts at 456.

<a id="api-95b95effd33d1b06"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_f_zero`

```lean
theorem TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation_f_zero {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : (filteredFlasqueResolutionDiagramAugmentation F).f 0 = F.whiskerLeft toFlasqueEnvelope
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L450-L454) · native range starts at 450.

<a id="api-1d1778d7e6b4cece"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation`

```lean
noncomputable def TopCat.Sheaf.filteredFlasqueResolutionDiagramAugmentation {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : (CochainComplex.single₀ (CategoryTheory.Functor I (Sheaf AddCommGrpCat X))).obj F ⟶ filteredFlasqueResolutionComplexDiagram F
```

**Native source docstring:**

The pointwise flasque-resolution augmentations, assembled in the category
of diagrams.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L425-L447) · native range starts at 425.

<a id="api-14ee62d1a334decf"></a>

### `TopCat.Sheaf.filteredFlasqueResolutionComplexDiagram`

```lean
noncomputable abbrev TopCat.Sheaf.filteredFlasqueResolutionComplexDiagram {X : TopCat} {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (F : CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) : CochainComplex (CategoryTheory.Functor I (Sheaf AddCommGrpCat X)) ℕ
```

**Native source docstring:**

The functorial flasque resolutions of a diagram of sheaves, viewed as a
complex in the category of diagrams.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L417-L423) · native range starts at 417.

<a id="api-02409ded08d2771f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology_hom_naturality_assoc {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) {f : A ⟶ B} (φ : R.Hom R' f) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj R'.cocomplex).homology q ⟶ Z) : CategoryStruct.comp ((Sheaf.functorH (Opens.grothendieckTopology ↑X) q).map f) (CategoryStruct.comp (R'.positiveIsoSectionsHomology q hq).hom h) = CategoryStruct.comp (R.positiveIsoSectionsHomology q hq).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) q) h)
```

**Native source docstring:**

The terminal-sections homology comparison is natural in maps of acyclic
resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L386-L386) · native range starts at 386.

<a id="api-61da8c4ce0573bbe"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology_hom_naturality {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) {f : A ⟶ B} (φ : R.Hom R' f) (q : ℕ) (hq : 0 < q) : CategoryStruct.comp ((Sheaf.functorH (Opens.grothendieckTopology ↑X) q).map f) (R'.positiveIsoSectionsHomology q hq).hom = CategoryStruct.comp (R.positiveIsoSectionsHomology q hq).hom (HomologicalComplex.homologyMap (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) q)
```

**Native source docstring:**

The terminal-sections homology comparison is natural in maps of acyclic
resolutions.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L384-L409) · native range starts at 384.

<a id="api-a825ca6863a457f3"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality_assoc {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) (f : R.cocomplex ⟶ R'.cocomplex) (q : ℕ) {Z : AddCommGrpCat} (h : (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj R'.cocomplex).homology q ⟶ Z) : CategoryStruct.comp (HomologicalComplex.homologyMap (R.homComplexMap R' f) q) (CategoryStruct.comp (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex TopCat.Sheaf.coyonedaIsoSections (ComplexShape.up ℕ)).app R'.cocomplex) q).hom h) = CategoryStruct.comp (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex TopCat.Sheaf.coyonedaIsoSections (ComplexShape.up ℕ)).app R.cocomplex) q).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map f) q) h)
```

**Native source docstring:**

Naturality on homology of the termwise additive-coyoneda/terminal-sections
comparison.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L345-L345) · native range starts at 345.

<a id="api-88e725c01eb9a8dd"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.coyonedaIsoSectionsHomology_hom_naturality {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) (f : R.cocomplex ⟶ R'.cocomplex) (q : ℕ) : CategoryStruct.comp (HomologicalComplex.homologyMap (R.homComplexMap R' f) q) (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex TopCat.Sheaf.coyonedaIsoSections (ComplexShape.up ℕ)).app R'.cocomplex) q).hom = CategoryStruct.comp (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex TopCat.Sheaf.coyonedaIsoSections (ComplexShape.up ℕ)).app R.cocomplex) q).hom (HomologicalComplex.homologyMap (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map f) q)
```

**Native source docstring:**

Naturality on homology of the termwise additive-coyoneda/terminal-sections
comparison.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L343-L381) · native range starts at 343.

<a id="api-359ae2e2cc31e3af"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_hom_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_hom_naturality_assoc {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) {f : A ⟶ B} (φ : R.Hom R' f) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology R'.homComplex q ⟶ Z) : CategoryStruct.comp ((Sheaf.functorH (Opens.grothendieckTopology ↑X) q).map f) (CategoryStruct.comp (R'.extPositiveIsoHomologyIso q hq).hom h) = CategoryStruct.comp (R.extPositiveIsoHomologyIso q hq).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (R.homComplexMap R' φ.hom) q) h)
```

**Native source docstring:**

Morphism form of naturality for the positive-degree acyclic-resolution
comparison.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L325-L325) · native range starts at 325.

<a id="api-1fca340d641ca4fd"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_hom_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomology_hom_naturality {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A B : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (R' : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) B) {f : A ⟶ B} (φ : R.Hom R' f) (q : ℕ) (hq : 0 < q) : CategoryStruct.comp ((Sheaf.functorH (Opens.grothendieckTopology ↑X) q).map f) (R'.extPositiveIsoHomologyIso q hq).hom = CategoryStruct.comp (R.extPositiveIsoHomologyIso q hq).hom (HomologicalComplex.homologyMap (R.homComplexMap R' φ.hom) q)
```

**Native source docstring:**

Morphism form of naturality for the positive-degree acyclic-resolution
comparison.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L323-L341) · native range starts at 323.

<a id="api-2077054d620a8c2f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.positiveIsoSectionsHomology {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (q : ℕ) (hq : 0 < q) : (Sheaf.functorH (Opens.grothendieckTopology ↑X) q).obj A ≅ (((SheafCohomology.CompactOpenSections.sections ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology q
```

**Native source docstring:**

Positive-degree cohomology computed by an acyclic resolution is the
homology of that resolution after taking terminal-open sections.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L306-L321) · native range starts at 306.

<a id="api-c52605b952e83421"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomologyIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.extPositiveIsoHomologyIso {X : TopCat} [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {A : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (R : AcyclicResolution ((constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) A) (q : ℕ) (hq : 0 < q) : (Sheaf.functorH (Opens.grothendieckTopology ↑X) q).obj A ≅ HomologicalComplex.homology R.homComplex q
```

**Native source docstring:**

The additive equivalence computing positive-degree Ext from an acyclic
resolution, packaged as an isomorphism with the exact bundled source object.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L292-L304) · native range starts at 292.

<a id="api-6ffce418ec8fd6b7"></a>

### `TopCat.Sheaf.coyonedaIsoSections`

```lean
noncomputable def TopCat.Sheaf.coyonedaIsoSections {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] : CategoryTheory.preadditiveCoyoneda.obj (Opposite.op ((CategoryTheory.constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ))) ≅ SheafCohomology.CompactOpenSections.sections ⊤
```

**Native source docstring:**

Additive coyoneda from the constant integral sheaf is naturally terminal-
open sections.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L279-L290) · native range starts at 279.

<a id="api-2529338811630c7b"></a>

### `HomologicalComplex.homologyColimitIso_hom_ι_assoc`

```lean
theorem HomologicalComplex.homologyColimitIso_hom_ι_assoc {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (n : κ) [CategoryTheory.Limits.colim.PreservesLeftHomologyOf ((ofFunctor D).sc n)] [CategoryTheory.Limits.colim.PreservesRightHomologyOf ((ofFunctor D).sc n)] (t : T) {Z : A} (h : (CategoryTheory.Limits.colimit D).homology n ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (D.comp (homologyFunctor A shape n)) t) (CategoryTheory.CategoryStruct.comp (homologyColimitIso D n).hom h) = CategoryTheory.CategoryStruct.comp (homologyMap (CategoryTheory.Limits.colimit.ι D t) n) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L224-L224) · native range starts at 224.

<a id="api-6c392edf9258bf77"></a>

### `HomologicalComplex.homologyColimitIso_hom_ι`

```lean
theorem HomologicalComplex.homologyColimitIso_hom_ι {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (n : κ) [CategoryTheory.Limits.colim.PreservesLeftHomologyOf ((ofFunctor D).sc n)] [CategoryTheory.Limits.colim.PreservesRightHomologyOf ((ofFunctor D).sc n)] (t : T) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (D.comp (homologyFunctor A shape n)) t) (homologyColimitIso D n).hom = homologyMap (CategoryTheory.Limits.colimit.ι D t) n
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L224-L261) · native range starts at 224.

<a id="api-05016a287bdb4278"></a>

### `HomologicalComplex.pointwiseHomologyIso_hom_app`

```lean
theorem HomologicalComplex.pointwiseHomologyIso_hom_app {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (n : κ) (t : T) : (pointwiseHomologyIso D n).hom.app t = (((ofFunctor D).sc n).mapHomologyIso ((CategoryTheory.evaluation T A).obj t)).hom
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L209-L221) · native range starts at 209.

<a id="api-a9a522d73f84d104"></a>

### `HomologicalComplex.homologyColimitIso`

```lean
noncomputable def HomologicalComplex.homologyColimitIso {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (n : κ) [CategoryTheory.Limits.colim.PreservesLeftHomologyOf ((ofFunctor D).sc n)] : CategoryTheory.Limits.colimit (D.comp (homologyFunctor A shape n)) ≅ (CategoryTheory.Limits.colimit D).homology n
```

**Native source docstring:**

Homology commutes with a colimit when the colimit functor preserves the
relevant homology short complex.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L196-L205) · native range starts at 196.

<a id="api-2ffcfc05d8868c30"></a>

### `HomologicalComplex.ofFunctorColimitι_comp_ofFunctorColimIso_hom_assoc`

```lean
theorem HomologicalComplex.ofFunctorColimitι_comp_ofFunctorColimIso_hom_assoc {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (t : T) {Z : HomologicalComplex A shape} (h : CategoryTheory.Limits.colimit D ⟶ Z) : CategoryTheory.CategoryStruct.comp (ofFunctorColimitι D t) (CategoryTheory.CategoryStruct.comp (ofFunctorColimIso D).hom h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι D t) h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L187-L187) · native range starts at 187.

<a id="api-025b92b04b96ea7d"></a>

### `HomologicalComplex.ofFunctorColimitι_comp_ofFunctorColimIso_hom`

```lean
theorem HomologicalComplex.ofFunctorColimitι_comp_ofFunctorColimIso_hom {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (t : T) : CategoryTheory.CategoryStruct.comp (ofFunctorColimitι D t) (ofFunctorColimIso D).hom = CategoryTheory.Limits.colimit.ι D t
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L187-L194) · native range starts at 187.

<a id="api-edec9f855f2c9946"></a>

### `HomologicalComplex.ofFunctorColimIso`

```lean
noncomputable def HomologicalComplex.ofFunctorColimIso {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) : (CategoryTheory.Limits.colim.mapHomologicalComplex shape).obj (ofFunctor D) ≅ CategoryTheory.Limits.colimit D
```

**Native source docstring:**

The degreewise colimit of the packaged complex is canonically the colimit
of the original diagram of complexes.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L151-L185) · native range starts at 151.

<a id="api-16e58f0a60f783a0"></a>

### `HomologicalComplex.ofFunctorColimitι`

```lean
noncomputable def HomologicalComplex.ofFunctorColimitι {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} [CategoryTheory.Limits.HasColimitsOfShape T A] (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (t : T) : D.obj t ⟶ (CategoryTheory.Limits.colim.mapHomologicalComplex shape).obj (ofFunctor D)
```

**Native source docstring:**

The canonical map from one complex in a diagram to the degreewise
colimit of the packaged diagram.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L140-L148) · native range starts at 140.

<a id="api-ad08ffccdb21db27"></a>

### `HomologicalComplex.evaluationToColim`

```lean
noncomputable def HomologicalComplex.evaluationToColim {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Limits.HasColimitsOfShape T A] (t : T) : (CategoryTheory.evaluation T A).obj t ⟶ CategoryTheory.Limits.colim
```

**Native source docstring:**

The canonical natural transformation from evaluation at one diagram
stage to the colimit functor.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L133-L138) · native range starts at 133.

<a id="api-8ddda93c48e85718"></a>

### `HomologicalComplex.pointwiseHomologyIso`

```lean
noncomputable def HomologicalComplex.pointwiseHomologyIso {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} (D : CategoryTheory.Functor T (HomologicalComplex A shape)) (n : κ) : D.comp (homologyFunctor A shape n) ≅ (ofFunctor D).homology n
```

**Native source docstring:**

Pointwise homology of a diagram of complexes is naturally the homology
object of the corresponding complex in the functor category.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L122-L129) · native range starts at 122.

<a id="api-52bd74a718f13c13"></a>

### `HomologicalComplex.asFunctorHomologyIso`

```lean
noncomputable def HomologicalComplex.asFunctorHomologyIso {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} (K : HomologicalComplex (CategoryTheory.Functor T A) shape) (n : κ) : K.asFunctor.comp (homologyFunctor A shape n) ≅ K.homology n
```

**Native source docstring:**

Homology after evaluating a complex of functors is naturally the
evaluation of its functor-category homology object.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L105-L120) · native range starts at 105.

<a id="api-ece09fd3baac40b1"></a>

### `HomologicalComplex.ofFunctorAsFunctorIso`

```lean
def HomologicalComplex.ofFunctorAsFunctorIso {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} (D : CategoryTheory.Functor T (HomologicalComplex A shape)) : (ofFunctor D).asFunctor ≅ D
```

**Native source docstring:**

Evaluation of the packaged complex recovers the original complex.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L90-L102) · native range starts at 90.

<a id="api-036271b68c832678"></a>

### `HomologicalComplex.ofFunctor`

```lean
def HomologicalComplex.ofFunctor {T : Type uT} [CategoryTheory.Category.{vT, uT} T] {A : Type uA} [CategoryTheory.Category.{vA, uA} A] [CategoryTheory.Abelian A] {κ : Type uκ} {shape : ComplexShape κ} (D : CategoryTheory.Functor T (HomologicalComplex A shape)) : HomologicalComplex (CategoryTheory.Functor T A) shape
```

**Native source docstring:**

Package a functor to complexes as a complex in the functor category.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L75-L88) · native range starts at 75.

<a id="api-99b4109909922d7c"></a>

### `HomologicalComplex.colimMapIso`

```lean
noncomputable def HomologicalComplex.colimMapIso {I : Type uI} [CategoryTheory.Category.{vI, uI} I] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] [CategoryTheory.Preadditive C] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] [CategoryTheory.Preadditive D] [CategoryTheory.Limits.HasColimitsOfShape I C] [CategoryTheory.Limits.HasColimitsOfShape I D] {ι : Type uι} {c : ComplexShape ι} (G : CategoryTheory.Functor C D) [G.Additive] (K : HomologicalComplex (CategoryTheory.Functor I C) c) [∀ (n : ι), CategoryTheory.Limits.PreservesColimit (K.X n) G] : (CategoryTheory.Limits.colim.mapHomologicalComplex c).obj ((((CategoryTheory.Functor.whiskeringRight I C D).obj G).mapHomologicalComplex c).obj K) ≅ (G.mapHomologicalComplex c).obj ((CategoryTheory.Limits.colim.mapHomologicalComplex c).obj K)
```

**Native source docstring:**

The canonical comparison is an isomorphism when the mapped functor
preserves the colimit of every term.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L57-L65) · native range starts at 57.

<a id="api-de6f960fcb78c6ce"></a>

### `HomologicalComplex.colimMapComparison_isIso`

```lean
instance HomologicalComplex.colimMapComparison_isIso {I : Type uI} [CategoryTheory.Category.{vI, uI} I] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] [CategoryTheory.Preadditive C] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] [CategoryTheory.Preadditive D] [CategoryTheory.Limits.HasColimitsOfShape I C] [CategoryTheory.Limits.HasColimitsOfShape I D] {ι : Type uι} {c : ComplexShape ι} (G : CategoryTheory.Functor C D) [G.Additive] (K : HomologicalComplex (CategoryTheory.Functor I C) c) [∀ (n : ι), CategoryTheory.Limits.PreservesColimit (K.X n) G] : CategoryTheory.IsIso (colimMapComparison G K)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L48-L55) · native range starts at 48.

<a id="api-a110bcac9dc18972"></a>

### `HomologicalComplex.colimMapComparison`

```lean
noncomputable def HomologicalComplex.colimMapComparison {I : Type uI} [CategoryTheory.Category.{vI, uI} I] {C : Type uC} [CategoryTheory.Category.{vC, uC} C] [CategoryTheory.Preadditive C] {D : Type uD} [CategoryTheory.Category.{vD, uD} D] [CategoryTheory.Preadditive D] [CategoryTheory.Limits.HasColimitsOfShape I C] [CategoryTheory.Limits.HasColimitsOfShape I D] {ι : Type uι} {c : ComplexShape ι} (G : CategoryTheory.Functor C D) [G.Additive] (K : HomologicalComplex (CategoryTheory.Functor I C) c) : (CategoryTheory.Limits.colim.mapHomologicalComplex c).obj ((((CategoryTheory.Functor.whiskeringRight I C D).obj G).mapHomologicalComplex c).obj K) ⟶ (G.mapHomologicalComplex c).obj ((CategoryTheory.Limits.colim.mapHomologicalComplex c).obj K)
```

**Native source docstring:**

The canonical comparison from the degreewise colimit after mapping a
complex of diagrams to mapping its degreewise colimit.

[Frozen source](../SheafCohomology/FilteredColimitFunctorH.lean#L38-L46) · native range starts at 38.

## `SheafCohomology.FlasqueAcyclicResolution`

Scope: subject module.

<a id="api-ac83fbbc9678abbf"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionHom`

```lean
noncomputable def TopCat.Sheaf.flasqueAcyclicResolutionHom {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : F.flasqueAcyclicResolution.Hom G.flasqueAcyclicResolution f
```

**Native source docstring:**

Functoriality of the flasque resolution gives a map of its packaged
acyclic resolutions above every map of sheaves.

[Frozen source](../SheafCohomology/FlasqueAcyclicResolution.lean#L56-L72) · native range starts at 56.

<a id="api-ede3e77a8db0597a"></a>

### `TopCat.Sheaf.flasqueResolutionNat_map_f_zero`

```lean
theorem TopCat.Sheaf.flasqueResolutionNat_map_f_zero {X : TopCat} {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : ((HomologicalComplex.asFunctor flasqueResolutionNat).map f).f 0 = flasqueEnvelopeFunctor.map f
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicResolution.lean#L48-L53) · native range starts at 48.

<a id="api-e56741bc707017eb"></a>

### `TopCat.Sheaf.flasqueAcyclicResolution`

```lean
noncomputable def TopCat.Sheaf.flasqueAcyclicResolution {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) : CategoryTheory.Abelian.Ext.AcyclicResolution ((CategoryTheory.constantSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).obj ↧(ULift.{0, 0} ℤ)) F
```

**Native source docstring:**

The functorial flasque resolution, packaged as a resolution acyclic for
the Ext functor defining sheaf cohomology.

[Frozen source](../SheafCohomology/FlasqueAcyclicResolution.lean#L30-L46) · native range starts at 30.

## `SheafCohomology.FlasqueAcyclicSections`

Scope: subject module.

<a id="api-e7dd638e7d85028f"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology_hom_naturality_assoc {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology G.flasqueResolutionSections q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (flasqueAcyclicResolutionExtZeroComplexMap f) q) (CategoryTheory.CategoryStruct.comp (G.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology q).hom h) = CategoryTheory.CategoryStruct.comp (F.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (flasqueResolutionSectionsMap f) q) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L94-L94) · native range starts at 94.

<a id="api-4b765f8ec140516b"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology_hom_naturality`

```lean
theorem TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology_hom_naturality {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (flasqueAcyclicResolutionExtZeroComplexMap f) q) (G.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology q).hom = CategoryTheory.CategoryStruct.comp (F.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology q).hom (HomologicalComplex.homologyMap (flasqueResolutionSectionsMap f) q)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L94-L112) · native range starts at 94.

<a id="api-d52d3e0789d95d98"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) (q : ℕ) : HomologicalComplex.homology F.flasqueAcyclicResolution.extZeroComplex q ≅ HomologicalComplex.homology F.flasqueResolutionSections q
```

**Native source docstring:**

The induced identification of the homology of the degree-zero Ext complex
with the homology of terminal-open sections.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L85-L92) · native range starts at 85.

<a id="api-8a2094b835b95d29"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality_assoc {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) {Z : CochainComplex AddCommGrpCat ℕ} (h : G.flasqueResolutionSections ⟶ Z) : CategoryTheory.CategoryStruct.comp (flasqueAcyclicResolutionExtZeroComplexMap f) (CategoryTheory.CategoryStruct.comp G.flasqueAcyclicResolutionExtZeroComplexIsoSections.hom h) = CategoryTheory.CategoryStruct.comp F.flasqueAcyclicResolutionExtZeroComplexIsoSections.hom (CategoryTheory.CategoryStruct.comp (flasqueResolutionSectionsMap f) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L73-L73) · native range starts at 73.

<a id="api-8fad77ec14bf5707"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality`

```lean
theorem TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : CategoryTheory.CategoryStruct.comp (flasqueAcyclicResolutionExtZeroComplexMap f) G.flasqueAcyclicResolutionExtZeroComplexIsoSections.hom = CategoryTheory.CategoryStruct.comp F.flasqueAcyclicResolutionExtZeroComplexIsoSections.hom (flasqueResolutionSectionsMap f)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L73-L83) · native range starts at 73.

<a id="api-096cf189f82ed797"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections`

```lean
noncomputable def TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexIsoSections {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) : F.flasqueAcyclicResolution.extZeroComplex ≅ F.flasqueResolutionSections
```

**Native source docstring:**

The degree-zero Ext complex of the packaged flasque acyclic resolution is
canonically the complex of its terminal-open sections.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L63-L71) · native range starts at 63.

<a id="api-78ad0f581d339419"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexMap_eq`

```lean
theorem TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexMap_eq {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : flasqueAcyclicResolutionExtZeroComplexMap f = F.flasqueAcyclicResolution.extZeroComplexMap G.flasqueAcyclicResolution (flasqueAcyclicResolutionHom f).hom
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L55-L61) · native range starts at 55.

<a id="api-a5af11fbdf3482ff"></a>

### `TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexMap`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueAcyclicResolutionExtZeroComplexMap {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : F.flasqueAcyclicResolution.extZeroComplex ⟶ G.flasqueAcyclicResolution.extZeroComplex
```

**Native source docstring:**

A sheaf morphism induces the corresponding map between the degree-zero
Ext complexes of their packaged flasque acyclic resolutions.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L43-L52) · native range starts at 43.

<a id="api-b9d9f53b80f0962d"></a>

### `TopCat.Sheaf.flasqueResolutionSectionsMap`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueResolutionSectionsMap {X : TopCat} {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) : F.flasqueResolutionSections ⟶ G.flasqueResolutionSections
```

**Native source docstring:**

A sheaf morphism induces the corresponding map between the complexes of
terminal-open sections of their functorial flasque resolutions.

[Frozen source](../SheafCohomology/FlasqueAcyclicSections.lean#L34-L41) · native range starts at 34.

## `SheafCohomology.FlasqueResolution`

Scope: subject module.

<a id="api-10dfc371e1a6ccf7"></a>

### `TopCat.Sheaf.flasqueEnvelopeConnectingIso`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeConnectingIso {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) : flasqueEnvelopeQuotientFunctor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (q + 1)) ≅ CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (q + 1 + 1)
```

**Native source docstring:**

The positive-degree connecting isomorphism for the functorial envelope is
natural in the input sheaf.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L863-L878) · native range starts at 863.

<a id="api-7b584ef9324f222f"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexMap`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeShortComplexMap {X : TopCat} {A B : Sheaf AddCommGrpCat X} (f : A ⟶ B) : A.flasqueEnvelopeShortComplex ⟶ B.flasqueEnvelopeShortComplex
```

**Native source docstring:**

A sheaf morphism induces the corresponding morphism between its first
functorial flasque-envelope short complexes.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L852-L861) · native range starts at 852.

<a id="api-2534391081c22fba"></a>

### `TopCat.Sheaf.derivedSuccIsoFlasqueResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.derivedSuccIsoFlasqueResolutionSectionsHomology {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) (n : ℕ) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (n + 1)).obj A ≅ HomologicalComplex.homology A.flasqueResolutionSections (n + 1)
```

**Native source docstring:**

In every positive degree, derived sheaf cohomology agrees with the homology
of terminal-open sections of the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L838-L848) · native range starts at 838.

<a id="api-415747f5b2b9c0f0"></a>

### `TopCat.Sheaf.derivedOneIsoFlasqueResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.derivedOneIsoFlasqueResolutionSectionsHomology {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 1).obj A.flasqueEnvelopeShortComplex.X₁ ≅ HomologicalComplex.homology A.flasqueResolutionSections 1
```

**Native source docstring:**

In degree one, derived sheaf cohomology agrees with the homology of
terminal-open sections of the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L827-L836) · native range starts at 827.

<a id="api-a62e8504b19c844d"></a>

### `TopCat.Sheaf.flasqueEnvelopeDerivedOneIsoCokernelSections`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeDerivedOneIsoCokernelSections {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 1).obj A.flasqueEnvelopeShortComplex.X₁ ≅ CategoryTheory.Limits.cokernel (terminalSectionsFunctor.map A.flasqueEnvelopeShortComplex.g)
```

**Native source docstring:**

The first derived cohomology group is the cokernel of the first envelope
projection after evaluation on the terminal open.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L815-L825) · native range starts at 815.

<a id="api-89b76742aa80cc49"></a>

### `TopCat.Sheaf.flasqueEnvelopeCokernelHZeroIsoCokernelSections`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeCokernelHZeroIsoCokernelSections {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) : CategoryTheory.Limits.cokernel ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 0).map A.flasqueEnvelopeShortComplex.g) ≅ CategoryTheory.Limits.cokernel (terminalSectionsFunctor.map A.flasqueEnvelopeShortComplex.g)
```

**Native source docstring:**

Transport the degree-zero cokernel across the natural isomorphism between
degree-zero derived cohomology and terminal-open sections.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L791-L813) · native range starts at 791.

<a id="api-7763b2e57eb772e6"></a>

### `TopCat.Sheaf.flasqueEnvelopeDerivedOneIsoCokernelHZero`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeDerivedOneIsoCokernelHZero {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 1).obj A.flasqueEnvelopeShortComplex.X₁ ≅ CategoryTheory.Limits.cokernel ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 0).map A.flasqueEnvelopeShortComplex.g)
```

**Native source docstring:**

The first derived cohomology group is the cokernel of the degree-zero
cohomology map induced by the first envelope projection.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L770-L789) · native range starts at 770.

<a id="api-be565cabe8481ddc"></a>

### `TopCat.Sheaf.flasqueEnvelopeDerivedIterateIso`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeDerivedIterateIso {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) (n : ℕ) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (n + 1)).obj A ≅ (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) 1).obj ((flasqueEnvelopeQuotientIterate n).obj A)
```

**Native source docstring:**

Iterating the positive-degree dimension shift identifies `H^(n+1)(A)`
with `H^1(Q^n(A))`.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L752-L768) · native range starts at 752.

<a id="api-635366ce17bda08b"></a>

### `TopCat.Sheaf.flasqueEnvelopeQuotientIterate_obj_obj`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeQuotientIterate_obj_obj {X : TopCat} (A : Sheaf AddCommGrpCat X) (n : ℕ) : (flasqueEnvelopeQuotientIterate n).obj (flasqueEnvelopeQuotientFunctor.obj A) = (flasqueEnvelopeQuotientIterate (n + 1)).obj A
```

**Native source docstring:**

Applying `Q^n` after one application of `Q` agrees objectwise with the
chosen `Q^(n+1)` iterate.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L735-L750) · native range starts at 735.

<a id="api-7d89a5cb8b6071ba"></a>

### `TopCat.Sheaf.flasqueEnvelopeDerivedSuccIso`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeDerivedSuccIso {X : TopCat} [CompactSpace ↑X] [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (A : Sheaf AddCommGrpCat X) (q : ℕ) : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (q + 1 + 1)).obj A ≅ (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑X) (q + 1)).obj (flasqueEnvelopeQuotientFunctor.obj A)
```

**Native source docstring:**

Positive-degree dimension shift through one functorial flasque envelope:
`H^(q+2)(A)` is `H^(q+1)(Q(A))`.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L710-L731) · native range starts at 710.

<a id="api-13f3a419d6cf2b4d"></a>

### `TopCat.Sheaf.flasqueResolutionSectionsHomologyIsoCokernel'`

```lean
noncomputable def TopCat.Sheaf.flasqueResolutionSectionsHomologyIsoCokernel' {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : HomologicalComplex.homology F.flasqueResolutionSections (n + 1) ≅ CategoryTheory.Limits.cokernel ((toFlasqueEnvelopeQuotient.app ((flasqueEnvelopeQuotientIterate n).obj F)).hom.app (Opposite.op ⊤))
```

**Native source docstring:**

The actual degree-`n + 1` homology of global sections of the functorial
flasque resolution is the same cokernel.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L686-L696) · native range starts at 686.

<a id="api-e9d75a9dc7530af8"></a>

### `TopCat.Sheaf.flasqueResolutionSectionsHomologyIsoCokernel`

```lean
noncomputable def TopCat.Sheaf.flasqueResolutionSectionsHomologyIsoCokernel {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : (HomologicalComplex.sc' F.flasqueResolutionSections n (n + 1) (n + 2)).homology ≅ CategoryTheory.Limits.cokernel ((toFlasqueEnvelopeQuotient.app ((flasqueEnvelopeQuotientIterate n).obj F)).hom.app (Opposite.op ⊤))
```

**Native source docstring:**

In degree `n + 1`, the homology of global sections of the functorial
flasque resolution is the cokernel of the degree-`n` envelope projection on
global sections.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L673-L684) · native range starts at 673.

<a id="api-61556a2f6b8624ec"></a>

### `TopCat.Sheaf.flasqueResolutionSectionsScIso`

```lean
noncomputable def TopCat.Sheaf.flasqueResolutionSectionsScIso {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : HomologicalComplex.sc' F.flasqueResolutionSections n (n + 1) (n + 2) ≅ ((flasqueEnvelopeQuotientIterate n).obj F).flasqueEnvelopeSectionsShortComplex
```

**Native source docstring:**

The three-term segment of the global-sections resolution agrees with the
arbitrary-sheaf envelope segment applied to the `n`th quotient iterate.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L650-L671) · native range starts at 650.

<a id="api-c60805e683054615"></a>

### `TopCat.Sheaf.flasqueResolutionSections`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueResolutionSections {X : TopCat} (F : Sheaf AddCommGrpCat X) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

The functorial flasque resolution after evaluation on the terminal open.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L644-L648) · native range starts at 644.

<a id="api-8758c7920752bc00"></a>

### `TopCat.Sheaf.instAdditiveAddCommGrpCatTerminalSectionsFunctor`

```lean
instance TopCat.Sheaf.instAdditiveAddCommGrpCatTerminalSectionsFunctor {X : TopCat} : terminalSectionsFunctor.Additive
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L631-L642) · native range starts at 631.

<a id="api-adbb653a0d30a618"></a>

### `TopCat.Sheaf.terminalSectionsFunctor`

```lean
noncomputable abbrev TopCat.Sheaf.terminalSectionsFunctor {X : TopCat} : CategoryTheory.Functor (Sheaf AddCommGrpCat X) AddCommGrpCat
```

**Native source docstring:**

Evaluation of a sheaf on the terminal open, as an additive functor.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L625-L629) · native range starts at 625.

<a id="api-fea086b5afe5dc6d"></a>

### `TopCat.Sheaf.flasqueEnvelopeSectionsHomologyIsoCokernel`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeSectionsHomologyIsoCokernel {X : TopCat} (A : Sheaf AddCommGrpCat X) : A.flasqueEnvelopeSectionsShortComplex.homology ≅ CategoryTheory.Limits.cokernel ((toFlasqueEnvelopeQuotient.app A).hom.app (Opposite.op ⊤))
```

**Native source docstring:**

The homology of three consecutive envelope terms on global sections is
the cokernel of the preceding quotient map on global sections.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L563-L623) · native range starts at 563.

<a id="api-983c964f4f57bc73"></a>

### `TopCat.Sheaf.flasqueEnvelopeSectionsShortComplex`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueEnvelopeSectionsShortComplex {X : TopCat} (A : Sheaf AddCommGrpCat X) : CategoryTheory.ShortComplex AddCommGrpCat
```

**Native source docstring:**

Three consecutive envelope terms after evaluation on the terminal open,
starting from an arbitrary sheaf `A`.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L531-L561) · native range starts at 531.

<a id="api-8c2201812b80547e"></a>

### `TopCat.Sheaf.sheafHom_app_mono`

```lean
instance TopCat.Sheaf.sheafHom_app_mono {X : TopCat} {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) [CategoryTheory.Mono f] (U : TopologicalSpace.Opens ↑X) : CategoryTheory.Mono (f.hom.app (Opposite.op U))
```

**Native source docstring:**

A monomorphism of sheaves of additive commutative groups is pointwise
monic on sections.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L522-L529) · native range starts at 522.

<a id="api-d92613915bed7898"></a>

### `CategoryTheory.ShortComplex.homologyIsoCokernelOfKernelFactorization`

```lean
noncomputable def CategoryTheory.ShortComplex.homologyIsoCokernelOfKernelFactorization {C : Type u} [Category.{v, u} C] [Abelian C] (S : ShortComplex C) (Q : C) (p : S.X₁ ⟶ Q) (i : Q ⟶ S.X₂) (hfi : CategoryStruct.comp p i = S.f) (hig : CategoryStruct.comp i S.g = 0) (hi : Limits.IsLimit (Limits.KernelFork.ofι i hig)) : S.homology ≅ Limits.cokernel p
```

**Native source docstring:**

If the cycles of a short complex are exhibited by a kernel `i : Q ⟶ X₂`
and the first differential factors as `p ≫ i`, then its homology is the
cokernel of `p`.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L488-L514) · native range starts at 488.

<a id="api-6c281b0cf4d387a9"></a>

### `TopCat.Sheaf.toFlasqueResolutionNat`

```lean
noncomputable def TopCat.Sheaf.toFlasqueResolutionNat {X : TopCat} : CochainComplex.single₀ (Sheaf AddCommGrpCat X) ⟶ HomologicalComplex.asFunctor flasqueResolutionNat
```

**Native source docstring:**

The canonical augmentations assemble naturally from sheaves concentrated
in degree zero to their functorial flasque resolutions.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L467-L478) · native range starts at 467.

<a id="api-14e68b78c6aa64e1"></a>

### `TopCat.Sheaf.toFlasqueResolution_quasiIso`

```lean
instance TopCat.Sheaf.toFlasqueResolution_quasiIso {X : TopCat} (F : Sheaf AddCommGrpCat X) : QuasiIso F.toFlasqueResolution
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L437-L465) · native range starts at 437.

<a id="api-9d17e62aec84161f"></a>

### `TopCat.Sheaf.toFlasqueResolution_f_zero`

```lean
theorem TopCat.Sheaf.toFlasqueResolution_f_zero {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.toFlasqueResolution.f 0 = toFlasqueEnvelope.app F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L432-L435) · native range starts at 432.

<a id="api-d4923a0e23d01d6f"></a>

### `TopCat.Sheaf.toFlasqueResolution`

```lean
noncomputable def TopCat.Sheaf.toFlasqueResolution {X : TopCat} (F : Sheaf AddCommGrpCat X) : (CochainComplex.single₀ (Sheaf AddCommGrpCat X)).obj F ⟶ F.flasqueResolution
```

**Native source docstring:**

The augmentation from a sheaf concentrated in degree zero to its
functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L412-L430) · native range starts at 412.

<a id="api-13231ed69afd24a1"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortExact`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortExact {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.Exact
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L396-L410) · native range starts at 396.

<a id="api-da181d9e3a8bffbc"></a>

### `TopCat.Sheaf.instMonoAddCommGrpCatFFlasqueResolutionAugmentedShortComplex`

```lean
instance TopCat.Sheaf.instMonoAddCommGrpCatFFlasqueResolutionAugmentedShortComplex {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.Mono F.flasqueResolutionAugmentedShortComplex.f
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L391-L394) · native range starts at 391.

<a id="api-10fbd85d8d684ad6"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_f`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_f {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.f = toFlasqueEnvelope.app F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L375-L375) · native range starts at 375.

<a id="api-a707d9dd7d326780"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₃`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₃ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.X₃ = flasqueEnvelopeFunctor.obj (flasqueEnvelopeQuotientFunctor.obj F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L375-L375) · native range starts at 375.

<a id="api-910afbe04fadf632"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₁`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₁ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.X₁ = (CategoryTheory.Functor.id (Sheaf AddCommGrpCat X)).obj F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L375-L375) · native range starts at 375.

<a id="api-796f748ff91a6215"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_g`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_g {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.g = CategoryTheory.CategoryStruct.comp (toFlasqueEnvelopeQuotient.app F) (toFlasqueEnvelope.app (flasqueEnvelopeQuotientFunctor.obj F))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L375-L375) · native range starts at 375.

<a id="api-f01c945351a22ddb"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₂`

```lean
theorem TopCat.Sheaf.flasqueResolutionAugmentedShortComplex_X₂ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueResolutionAugmentedShortComplex.X₂ = flasqueEnvelopeFunctor.obj F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L375-L375) · native range starts at 375.

<a id="api-b919e7aaa0a1ba28"></a>

### `TopCat.Sheaf.flasqueResolutionAugmentedShortComplex`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueResolutionAugmentedShortComplex {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The augmented degree-zero short complex of the functorial flasque
resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L373-L389) · native range starts at 373.

<a id="api-08f1a9420264cfd5"></a>

### `TopCat.Sheaf.flasqueResolution_exactAt_succ`

```lean
theorem TopCat.Sheaf.flasqueResolution_exactAt_succ {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : HomologicalComplex.ExactAt F.flasqueResolution (n + 1)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L317-L371) · native range starts at 317.

<a id="api-5446b6192f90dd38"></a>

### `TopCat.Sheaf.flasqueResolution_d_succ`

```lean
theorem TopCat.Sheaf.flasqueResolution_d_succ {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : F.flasqueResolution.d n (n + 1) = CategoryTheory.CategoryStruct.comp (toFlasqueEnvelopeQuotient.app ((flasqueEnvelopeQuotientIterate n).obj F)) (toFlasqueEnvelope.app ((flasqueEnvelopeQuotientIterate (n + 1)).obj F))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L306-L315) · native range starts at 306.

<a id="api-33b30d2cf88204e5"></a>

### `TopCat.Sheaf.flasqueResolution_isFlasque`

```lean
instance TopCat.Sheaf.flasqueResolution_isFlasque {X : TopCat} (F : Sheaf AddCommGrpCat X) (n : ℕ) : (F.flasqueResolution.X n).IsFlasque
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L298-L304) · native range starts at 298.

<a id="api-14a35df372911782"></a>

### `TopCat.Sheaf.flasqueResolution`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueResolution {X : TopCat} (F : Sheaf AddCommGrpCat X) : CochainComplex (Sheaf AddCommGrpCat X) ℕ
```

**Native source docstring:**

Evaluation of the functorial flasque resolution at a sheaf.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L293-L296) · native range starts at 293.

<a id="api-dc476871d82cde79"></a>

### `TopCat.Sheaf.flasqueResolutionNat`

```lean
noncomputable def TopCat.Sheaf.flasqueResolutionNat {X : TopCat} : CochainComplex (CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)) ℕ
```

**Native source docstring:**

The functorial stalk-skyscraper flasque resolution, before evaluation at
a particular sheaf.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L272-L291) · native range starts at 272.

<a id="api-3f2716271817ece8"></a>

### `TopCat.Sheaf.flasqueResolutionDifferential_comp_assoc`

```lean
theorem TopCat.Sheaf.flasqueResolutionDifferential_comp_assoc {X : TopCat} (n : ℕ) {Z : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)} (h : flasqueResolutionFunctor (n + 1 + 1) ⟶ Z) : CategoryTheory.CategoryStruct.comp (flasqueResolutionDifferential n) (CategoryTheory.CategoryStruct.comp (flasqueResolutionDifferential (n + 1)) h) = CategoryTheory.CategoryStruct.comp 0 h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L229-L229) · native range starts at 229.

<a id="api-7400e9c6113c7353"></a>

### `TopCat.Sheaf.flasqueResolutionDifferential_comp`

```lean
theorem TopCat.Sheaf.flasqueResolutionDifferential_comp {X : TopCat} (n : ℕ) : CategoryTheory.CategoryStruct.comp (flasqueResolutionDifferential n) (flasqueResolutionDifferential (n + 1)) = 0
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L229-L270) · native range starts at 229.

<a id="api-51927f61b0b0337a"></a>

### `TopCat.Sheaf.flasqueResolutionDifferential`

```lean
noncomputable def TopCat.Sheaf.flasqueResolutionDifferential {X : TopCat} (n : ℕ) : flasqueResolutionFunctor n ⟶ flasqueResolutionFunctor (n + 1)
```

**Native source docstring:**

The degree-`n` differential in the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L193-L227) · native range starts at 193.

<a id="api-de97a92dc21749d5"></a>

### `TopCat.Sheaf.flasqueResolutionFunctor`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueResolutionFunctor {X : TopCat} (n : ℕ) : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The degree-`n` functor in the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L188-L191) · native range starts at 188.

<a id="api-1fd9369b7a85993a"></a>

### `TopCat.Sheaf.flasqueEnvelopeQuotientIterate_succ`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeQuotientIterate_succ {X : TopCat} (n : ℕ) : flasqueEnvelopeQuotientIterate (n + 1) = (flasqueEnvelopeQuotientIterate n).comp flasqueEnvelopeQuotientFunctor
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L182-L186) · native range starts at 182.

<a id="api-3a99bd69afafbc98"></a>

### `TopCat.Sheaf.flasqueEnvelopeQuotientIterate_zero`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeQuotientIterate_zero {X : TopCat} : flasqueEnvelopeQuotientIterate 0 = CategoryTheory.Functor.id (Sheaf AddCommGrpCat X)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L178-L180) · native range starts at 178.

<a id="api-e9e7e87c1413009c"></a>

### `TopCat.Sheaf.flasqueEnvelopeQuotientIterate`

```lean
noncomputable def TopCat.Sheaf.flasqueEnvelopeQuotientIterate {X : TopCat} : ℕ → CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

Iterates of the quotient functor used in the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L171-L176) · native range starts at 171.

<a id="api-4c8c793a5af442bd"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortExact`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortExact {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.ShortExact
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L164-L169) · native range starts at 164.

<a id="api-8d3046ec037b6f47"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex_g`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplex_g {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.g = toFlasqueEnvelopeQuotient.app F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L156-L156) · native range starts at 156.

<a id="api-5c0f8ceddd63ed10"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex_X₃`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplex_X₃ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.X₃ = flasqueEnvelopeQuotientFunctor.obj F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L156-L156) · native range starts at 156.

<a id="api-f5eb17ac4748d9ea"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex_f`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplex_f {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.f = toFlasqueEnvelope.app F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L156-L156) · native range starts at 156.

<a id="api-9eedd9020366ce54"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex_X₁`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplex_X₁ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.X₁ = (CategoryTheory.Functor.id (Sheaf AddCommGrpCat X)).obj F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L156-L156) · native range starts at 156.

<a id="api-bb965785c1e2c03c"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex_X₂`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplex_X₂ {X : TopCat} (F : Sheaf AddCommGrpCat X) : F.flasqueEnvelopeShortComplex.X₂ = flasqueEnvelopeFunctor.obj F
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L156-L156) · native range starts at 156.

<a id="api-a6427fe4cb297030"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplex`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueEnvelopeShortComplex {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The first objectwise short complex in the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L155-L162) · native range starts at 155.

<a id="api-95ac30afe86b248a"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortExactNat`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortExactNat {X : TopCat} : flasqueEnvelopeShortComplexNat.ShortExact
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L150-L153) · native range starts at 150.

<a id="api-24b27ee9a31326fa"></a>

### `TopCat.Sheaf.instEpiFunctorAddCommGrpCatGFlasqueEnvelopeShortComplexNat`

```lean
instance TopCat.Sheaf.instEpiFunctorAddCommGrpCatGFlasqueEnvelopeShortComplexNat {X : TopCat} : CategoryTheory.Epi flasqueEnvelopeShortComplexNat.g
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L146-L148) · native range starts at 146.

<a id="api-74df3ebd2c80bb95"></a>

### `TopCat.Sheaf.instMonoFunctorAddCommGrpCatFFlasqueEnvelopeShortComplexNat`

```lean
instance TopCat.Sheaf.instMonoFunctorAddCommGrpCatFFlasqueEnvelopeShortComplexNat {X : TopCat} : CategoryTheory.Mono flasqueEnvelopeShortComplexNat.f
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L143-L144) · native range starts at 143.

<a id="api-922ed71601f4582d"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₃`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₃ {X : TopCat} : flasqueEnvelopeShortComplexNat.X₃ = flasqueEnvelopeQuotientFunctor
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L136-L136) · native range starts at 136.

<a id="api-a9661d112c8e979b"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₁`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₁ {X : TopCat} : flasqueEnvelopeShortComplexNat.X₁ = CategoryTheory.Functor.id (Sheaf AddCommGrpCat X)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L136-L136) · native range starts at 136.

<a id="api-f0cede7dc69f358d"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₂`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplexNat_X₂ {X : TopCat} : flasqueEnvelopeShortComplexNat.X₂ = flasqueEnvelopeFunctor
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L136-L136) · native range starts at 136.

<a id="api-1c6b7f8734006221"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat_f`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplexNat_f {X : TopCat} : flasqueEnvelopeShortComplexNat.f = toFlasqueEnvelope
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L136-L136) · native range starts at 136.

<a id="api-b763ac1be659b3ae"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat_g`

```lean
theorem TopCat.Sheaf.flasqueEnvelopeShortComplexNat_g {X : TopCat} : flasqueEnvelopeShortComplexNat.g = toFlasqueEnvelopeQuotient
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L136-L136) · native range starts at 136.

<a id="api-66bdd610ce8c7072"></a>

### `TopCat.Sheaf.flasqueEnvelopeShortComplexNat`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueEnvelopeShortComplexNat {X : TopCat} : CategoryTheory.ShortComplex (CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X))
```

**Native source docstring:**

The first short complex in the functorial flasque resolution.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L135-L141) · native range starts at 135.

<a id="api-ef433372758f0b1f"></a>

### `TopCat.Sheaf.toFlasqueEnvelopeQuotient_app_epi`

```lean
instance TopCat.Sheaf.toFlasqueEnvelopeQuotient_app_epi {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.Epi (toFlasqueEnvelopeQuotient.app F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L129-L133) · native range starts at 129.

<a id="api-10e6028e181ad006"></a>

### `TopCat.Sheaf.toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient_assoc`

```lean
theorem TopCat.Sheaf.toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient_assoc {X : TopCat} {Z : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)} (h : flasqueEnvelopeQuotientFunctor ⟶ Z) : CategoryTheory.CategoryStruct.comp toFlasqueEnvelope (CategoryTheory.CategoryStruct.comp toFlasqueEnvelopeQuotient h) = CategoryTheory.CategoryStruct.comp 0 h
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L123-L123) · native range starts at 123.

<a id="api-fcc4351784ba2f37"></a>

### `TopCat.Sheaf.toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient`

```lean
theorem TopCat.Sheaf.toFlasqueEnvelope_comp_toFlasqueEnvelopeQuotient {X : TopCat} : CategoryTheory.CategoryStruct.comp toFlasqueEnvelope toFlasqueEnvelopeQuotient = 0
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L123-L127) · native range starts at 123.

<a id="api-4d765f0c55982ad2"></a>

### `TopCat.Sheaf.toFlasqueEnvelopeQuotient`

```lean
noncomputable abbrev TopCat.Sheaf.toFlasqueEnvelopeQuotient {X : TopCat} : flasqueEnvelopeFunctor ⟶ flasqueEnvelopeQuotientFunctor
```

**Native source docstring:**

The natural projection onto the functorial quotient.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L117-L121) · native range starts at 117.

<a id="api-34716d1b7e0f70ae"></a>

### `TopCat.Sheaf.flasqueEnvelopeQuotientFunctor`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueEnvelopeQuotientFunctor {X : TopCat} : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The functorial quotient by the stalk-skyscraper flasque envelope.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L112-L115) · native range starts at 112.

<a id="api-af324bf60ee08a7d"></a>

### `TopCat.Sheaf.toFlasqueEnvelope_app_mono`

```lean
instance TopCat.Sheaf.toFlasqueEnvelope_app_mono {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.Mono (toFlasqueEnvelope.app F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L80-L110) · native range starts at 80.

<a id="api-c83bb394086847cb"></a>

### `TopCat.Sheaf.instIsFlasqueAddCommGrpCatObjFlasqueEnvelopeFunctor`

```lean
instance TopCat.Sheaf.instIsFlasqueAddCommGrpCatObjFlasqueEnvelopeFunctor {X : TopCat} (F : Sheaf AddCommGrpCat X) : (flasqueEnvelopeFunctor.obj F).IsFlasque
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L66-L78) · native range starts at 66.

<a id="api-8e725fe682927628"></a>

### `TopCat.Sheaf.toFlasqueEnvelope`

```lean
noncomputable abbrev TopCat.Sheaf.toFlasqueEnvelope {X : TopCat} : CategoryTheory.Functor.id (Sheaf AddCommGrpCat X) ⟶ flasqueEnvelopeFunctor
```

**Native source docstring:**

The adjunction units assemble to a natural map into the flasque envelope.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L61-L64) · native range starts at 61.

<a id="api-80b9eb58482009df"></a>

### `TopCat.Sheaf.flasqueEnvelopeFunctor`

```lean
noncomputable abbrev TopCat.Sheaf.flasqueEnvelopeFunctor {X : TopCat} : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The product of the stalk-skyscraper endofunctors over all points.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L56-L59) · native range starts at 56.

<a id="api-f14cd54a25e60c4d"></a>

### `TopCat.Sheaf.stalkSkyscraperFunctor`

```lean
noncomputable abbrev TopCat.Sheaf.stalkSkyscraperFunctor {X : TopCat} (x : ↑X) : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The stalk-skyscraper endofunctor at a point.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L49-L54) · native range starts at 49.

<a id="api-c8b30c1042439af5"></a>

### `TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology_1`

```lean
noncomputable def TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology_1 {X : TopCat} (x : ↑X) (U : TopologicalSpace.Opens ↑X) : Decidable (x ∈ U)
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/FlasqueResolution.lean#L38-L38) · native range starts at 38.

## `SheafCohomology.HigherDirectImageFilteredColimit`

Scope: subject module.

<a id="api-2b34581efd7c168b"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_ι`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_ι {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (q : ℕ) (i : I) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (F.comp ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q)) i) (CategoryTheory.Limits.colimit.post F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q)) = ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q).map (CategoryTheory.Limits.colimit.ι F i)
```

**Native source docstring:**

On every stage, the canonical comparison is characterized by the
corresponding right-derived image of the diagram's colimit leg.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L348-L358) · native range starts at 348.

<a id="api-5f6bf3226a922a96"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) : CategoryTheory.IsIso (CategoryTheory.Limits.colimit.post F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q))
```

**Native source docstring:**

The literal canonical comparison for right-derived pushforward is an
isomorphism in every natural degree.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L330-L343) · native range starts at 330.

<a id="api-d03870b67512a0a5"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_preservesColimit`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_preservesColimit {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) : CategoryTheory.Limits.PreservesColimit F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q)
```

**Native source docstring:**

Right-derived pushforward preserves a same-small-universe filtered colimit
in every natural degree.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L316-L328) · native range starts at 316.

<a id="api-5c990b83d92806c0"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.rightDerived_colimitPost_isIso_zero`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.rightDerived_colimitPost_isIso_zero {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) : CategoryTheory.IsIso (CategoryTheory.Limits.colimit.post F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived 0))
```

**Native source docstring:**

The literal degree-zero right-derived-pushforward comparison is an
isomorphism. Preservation is transported through mathlib's canonical
`rightDerivedZeroIsoSelf`, after proving it for pushforward itself.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L296-L314) · native range starts at 296.

<a id="api-089cbdc5af98bc5c"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.pushforward_colimitPost_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.pushforward_colimitPost_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) : CategoryTheory.IsIso (CategoryTheory.Limits.colimit.post F (pushforward f))
```

**Native source docstring:**

Under the degree-zero hypotheses, the canonical pushforward
comparison is an isomorphism.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L277-L287) · native range starts at 277.

<a id="api-7a1f3e48cafccd77"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison_eq_canonical`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison_eq_canonical {X Y : TopCat} (f : X ⟶ Y) {I : Type} [Preorder I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) : CategoryTheory.CategoryStruct.comp (CompactOpenSections.explicitSheafColimitIso (F.comp (pushforward f))).hom (CategoryTheory.Limits.colimit.post F (pushforward f)) = explicitPushforwardColimitComparison f F
```

**Native source docstring:**

The explicit comparison agrees with the canonical pushforward
`colimit.post` after identifying the explicit source with the chosen sheaf
colimit.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L190-L273) · native range starts at 190.

<a id="api-a40c009307499d1a"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) : CategoryTheory.IsIso (explicitPushforwardColimitComparison f F)
```

**Native source docstring:**

The explicit comparison is an isomorphism: on the compact-open basis its
underlying presheaf map is the compact-section comparison on the inverse
image.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L160-L184) · native range starts at 160.

<a id="api-6cb7a9ddccefd2de"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.explicitPushforwardColimitComparison {X Y : TopCat} (f : X ⟶ Y) {I : Type} [Preorder I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).obj (underlyingPushforwardPresheafColimit f F) ⟶ (pushforward f).obj (CategoryTheory.Limits.colimit F)
```

**Native source docstring:**

The comparison from the explicit sheafification model of the pushforward
colimit to the pushforward of the source colimit.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L141-L154) · native range starts at 141.

<a id="api-ce8d8864982fd5e3"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison_app_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison_app_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (V : TopologicalSpace.Opens ↑Y) (hV : IsCompact ↑V) : CategoryTheory.IsIso ((presheafPushforwardColimitComparison f F).app (Opposite.op V))
```

**Native source docstring:**

On a compact target open, the presheaf comparison is an isomorphism when
the inverse image is compact.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L120-L139) · native range starts at 120.

<a id="api-2d91e932f88f24e7"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison_app`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison_app {X Y : TopCat} (f : X ⟶ Y) {I : Type} [Preorder I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) (V : TopologicalSpace.Opens ↑Y) : (presheafPushforwardColimitComparison f F).app (Opposite.op V) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation (F.comp ((pushforward f).comp forgetY)) (Opposite.op V)).hom (CategoryTheory.Limits.colimit.post F (pushforwardSections f V))
```

**Native source docstring:**

On a target open, the presheaf comparison is the canonical comparison for
sections on its inverse image, after the pointwise-colimit isomorphism.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L95-L115) · native range starts at 95.

<a id="api-1c6fb1f8dee9f3aa"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.presheafPushforwardColimitComparison {X Y : TopCat} (f : X ⟶ Y) {I : Type} [Preorder I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) : underlyingPushforwardPresheafColimit f F ⟶ forgetY.obj ((pushforward f).obj (CategoryTheory.Limits.colimit F))
```

**Native source docstring:**

Before target sheafification, the pushforward comparison is induced by
the source colimit cocone.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L84-L89) · native range starts at 84.

<a id="api-43e56bc171ea484e"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.underlyingPushforwardPresheafColimit`

```lean
noncomputable abbrev SheafCohomology.HigherDirectImageFilteredColimit.underlyingPushforwardPresheafColimit {X Y : TopCat} (f : X ⟶ Y) {I : Type} [Preorder I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)) : TopCat.Presheaf AddCommGrpCat Y
```

**Native source docstring:**

The pointwise presheaf colimit underlying the explicit colimit of the
pushforward diagram.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L79-L82) · native range starts at 79.

<a id="api-bdee9ad416de48fc"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.pushforwardSections_eq`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.pushforwardSections_eq {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : pushforwardSections f V = preimageSections f V
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L75-L77) · native range starts at 75.

<a id="api-f46b04871c1a09ec"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.pushforwardSections`

```lean
abbrev SheafCohomology.HigherDirectImageFilteredColimit.pushforwardSections {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) AddCommGrpCat
```

**Native source docstring:**

Sections after pushforward, kept in the definitionally pointwise form.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L64-L70) · native range starts at 64.

<a id="api-ddb71253cd3fc9aa"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimageSections`

```lean
abbrev SheafCohomology.HigherDirectImageFilteredColimit.preimageSections {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) AddCommGrpCat
```

**Native source docstring:**

Sections on the inverse image of a target open.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L57-L62) · native range starts at 57.

<a id="api-cd791aca04526377"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.forgetY`

```lean
abbrev SheafCohomology.HigherDirectImageFilteredColimit.forgetY {Y : TopCat} : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat) (TopCat.Presheaf AddCommGrpCat Y)
```

**Native source docstring:**

Forgetful functor from sheaves on the target.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L49-L55) · native range starts at 49.

<a id="api-378df37a3602c941"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.pushforward`

```lean
abbrev SheafCohomology.HigherDirectImageFilteredColimit.pushforward {X Y : TopCat} (f : X ⟶ Y) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat)
```

**Native source docstring:**

Pushforward in the selected common universe.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimit.lean#L41-L47) · native range starts at 41.

## `SheafCohomology.HigherDirectImageFilteredColimitPositive`

Scope: subject module.

<a id="api-66e8508f1d6ad67f"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_factorization_rightDerived`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_factorization_rightDerived {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) (q : ℕ) (hq : 0 < q) : let L := TopCat.Sheaf.localCohomologyPresheafFunctor f q; let S := CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat; have e := TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived f q hq; CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post (F.comp L) S) (S.map (CategoryTheory.Limits.colimit.post F L))) (e.hom.app (CategoryTheory.Limits.colimit F)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft e.hom)) (CategoryTheory.Limits.colimit.post F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q))
```

**Native source docstring:**

The sheafification of the canonical local-cohomology-presheaf comparison,
including the canonical sheafification/colimit comparison, is exactly the
positive right-derived canonical comparison after transport by the accepted
natural isomorphism on the source and target.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L164-L184) · native range starts at 164.

<a id="api-0eea672f09f74a32"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_colimitPost_transport_rightDerived`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_colimitPost_transport_rightDerived {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) (q : ℕ) (hq : 0 < q) : have e := TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived f q hq; CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft e.hom)) (CategoryTheory.Limits.colimit.post F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q)) (e.hom.app (CategoryTheory.Limits.colimit F))
```

**Native source docstring:**

The canonical comparison for sheafified local cohomology transports to
the literal canonical comparison for positive-degree right-derived
pushforward. The equality is proved on every colimit cocone leg.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L146-L160) · native range starts at 146.

<a id="api-c615ecd0a640ae2f"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_sheafification_factorization`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_sheafification_factorization {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) (q : ℕ) : let L := TopCat.Sheaf.localCohomologyPresheafFunctor f q; let S := CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat; CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post (F.comp L) S) (S.map (CategoryTheory.Limits.colimit.post F L)) = CategoryTheory.Limits.colimit.post F (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q)
```

**Native source docstring:**

The canonical comparison for sheafified local cohomology is literally the
sheafification of the canonical presheaf comparison, preceded by the canonical
comparison expressing that sheafification preserves the presheaf colimit.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L131-L142) · native range starts at 131.

<a id="api-6bfb6d030cf316c2"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_preservesColimit_positive`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_preservesColimit_positive {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) [CategoryTheory.IsFiltered I] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) (hq : 0 < q) : CategoryTheory.Limits.PreservesColimit F ((TopCat.Sheaf.pushforward AddCommGrpCat f).rightDerived q)
```

**Native source docstring:**

In positive degree, right-derived pushforward preserves the same filtered
colimit, through the accepted natural comparison with sheafified local
cohomology.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L115-L125) · native range starts at 115.

<a id="api-962442c8e99a76fc"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_preservesColimit`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_preservesColimit {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) [CategoryTheory.IsFiltered I] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) : CategoryTheory.Limits.PreservesColimit F (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q)
```

**Native source docstring:**

Sheafified local cohomology preserves a same-small-universe filtered
colimit along a spectral map into a prespectral target.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L97-L113) · native range starts at 97.

<a id="api-34e383bd8589b595"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_colimitPost_map_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.sheafifiedLocalCohomology_colimitPost_map_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑Y] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) [CategoryTheory.IsFiltered I] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) : CategoryTheory.IsIso ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).map (CategoryTheory.Limits.colimit.post F (TopCat.Sheaf.localCohomologyPresheafFunctor f q)))
```

**Native source docstring:**

Sheafifying the canonical local-cohomology-presheaf comparison produces
an isomorphism, because it is already an isomorphism on the compact-open basis
of the prespectral target.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L84-L95) · native range starts at 84.

<a id="api-0fc398acdf8ed364"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_app_isIso`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.localCohomologyPresheaf_colimitPost_app_isIso {X Y : TopCat} (f : X ⟶ Y) [PrespectralSpace ↑X] [QuasiSeparatedSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (TopCat.Sheaf AddCommGrpCat X)) [CategoryTheory.IsFiltered I] (hf : IsSpectralMap ⇑(CategoryTheory.ConcreteCategory.hom f)) (q : ℕ) (V : TopologicalSpace.Opens ↑Y) (hV : IsCompact ↑V) : CategoryTheory.IsIso ((CategoryTheory.Limits.colimit.post F (TopCat.Sheaf.localCohomologyPresheafFunctor f q)).app (Opposite.op V))
```

**Native source docstring:**

At a compact open of the target, the canonical comparison for the local
cohomology presheaf is an isomorphism.

[Frozen source](../SheafCohomology/HigherDirectImageFilteredColimitPositive.lean#L53-L80) · native range starts at 53.

## `SheafCohomology.InjectiveResolutionNaturality`

Scope: subject module.

<a id="api-91fe74a9a42a0b81"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtPositiveIsoHomology_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtPositiveIsoHomology_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (q : ℕ) (hq : 0 < q) (x : Ext X A q) : ((ofInjectiveResolution X' I).extPositiveIsoHomology q hq) ((mk₀ g).comp x ⋯) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveHomComplexSourceMap I g) q)) (((ofInjectiveResolution X I).extPositiveIsoHomology q hq) x)
```

**Native source docstring:**

For a fixed injective resolution, the positive Ext/homology comparison is
contravariantly natural in the source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L736-L774) · native range starts at 736.

<a id="api-355a090995b67f27"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomology_eqToIso_source_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomology_eqToIso_source_naturality_apply {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) {m n : ℕ} (h : m = n) (z : ↑(HomologicalComplex.homology (ofInjectiveResolution X I).extZeroComplex m)) : (eqToIso ⋯).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) m)) z) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) n)) ((eqToIso ⋯).addCommGroupIsoToAddEquiv z)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L718-L733) · native range starts at 718.

<a id="api-2b839a394f40996b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtIsoCyclesZero_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtIsoCyclesZero_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (q : ℕ) (x : Ext X A q) : ((ofInjectiveResolution X' I).extIsoCyclesZero q) ((mk₀ g).comp x ⋯) = (mk₀ g).comp (((ofInjectiveResolution X I).extIsoCyclesZero q) x) ⋯
```

**Native source docstring:**

Transport to degree-zero cycles for a fixed injective resolution is
contravariantly natural in the source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L693-L716) · native range starts at 693.

<a id="api-a162c0eb9f81b7f2"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality_apply {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) (z : ↑(HomologicalComplex.homology (ofInjectiveResolution X I).extZeroComplex n)) : ((ofInjectiveResolution X' I).extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) n)) z) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveHomComplexSourceMap I g) n)) (((ofInjectiveResolution X I).extZeroHomologyIsoHomology n).addCommGroupIsoToAddEquiv z)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L675-L690) · native range starts at 675.

<a id="api-be69298653c15ef2"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (ofInjectiveResolution X' I).homComplex n ⟶ Z) : CategoryStruct.comp (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) n) (CategoryStruct.comp ((ofInjectiveResolution X' I).extZeroHomologyIsoHomology n).hom h) = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroHomologyIsoHomology n).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (injectiveHomComplexSourceMap I g) n) h)
```

**Native source docstring:**

The induced homology comparison between degree-zero Ext and additive
coyoneda for a fixed injective resolution is contravariantly natural in its
source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L659-L659) · native range starts at 659.

<a id="api-2cfe7c1d8cab86af"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroHomologyIsoHomology_hom_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : CategoryStruct.comp (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) n) ((ofInjectiveResolution X' I).extZeroHomologyIsoHomology n).hom = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroHomologyIsoHomology n).hom (HomologicalComplex.homologyMap (injectiveHomComplexSourceMap I g) n)
```

**Native source docstring:**

The induced homology comparison between degree-zero Ext and additive
coyoneda for a fixed injective resolution is contravariantly natural in its
source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L656-L673) · native range starts at 656.

<a id="api-191b5d46282f3537"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexIsoHomComplex_hom_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexIsoHomComplex_hom_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) {Z : CochainComplex AddCommGrpCat ℕ} (h : (ofInjectiveResolution X' I).homComplex ⟶ Z) : CategoryStruct.comp (injectiveExtZeroComplexSourceMap I g) (CategoryStruct.comp (ofInjectiveResolution X' I).extZeroComplexIsoHomComplex.hom h) = CategoryStruct.comp (ofInjectiveResolution X I).extZeroComplexIsoHomComplex.hom (CategoryStruct.comp (injectiveHomComplexSourceMap I g) h)
```

**Native source docstring:**

The termwise degree-zero Ext/additive-coyoneda complex comparison for a
fixed injective resolution is contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L642-L642) · native range starts at 642.

<a id="api-90d17327effcefe1"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexIsoHomComplex_hom_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexIsoHomComplex_hom_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) : CategoryStruct.comp (injectiveExtZeroComplexSourceMap I g) (ofInjectiveResolution X' I).extZeroComplexIsoHomComplex.hom = CategoryStruct.comp (ofInjectiveResolution X I).extZeroComplexIsoHomComplex.hom (injectiveHomComplexSourceMap I g)
```

**Native source docstring:**

The termwise degree-zero Ext/additive-coyoneda complex comparison for a
fixed injective resolution is contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L640-L653) · native range starts at 640.

<a id="api-4e483d685c943555"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCoyonedaIso_hom_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCoyonedaIso_hom_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) (Y : C) {Z : AddCommGrpCat} (h : (preadditiveCoyoneda.obj (Opposite.op X')).obj Y ⟶ Z) : CategoryStruct.comp (extSourceMap g 0 Y) (CategoryStruct.comp ((extZeroCoyonedaIso X').hom.app Y) h) = CategoryStruct.comp ((extZeroCoyonedaIso X).hom.app Y) (CategoryStruct.comp ((preadditiveCoyoneda.map g.op).app Y) h)
```

**Native source docstring:**

The degree-zero Ext/coyoneda comparison is contravariantly natural in its
source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L625-L625) · native range starts at 625.

<a id="api-567c47d38289a15c"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCoyonedaIso_hom_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.extZeroCoyonedaIso_hom_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) (Y : C) : CategoryStruct.comp (extSourceMap g 0 Y) ((extZeroCoyonedaIso X').hom.app Y) = CategoryStruct.comp ((extZeroCoyonedaIso X).hom.app Y) ((preadditiveCoyoneda.map g.op).app Y)
```

**Native source docstring:**

The degree-zero Ext/coyoneda comparison is contravariantly natural in its
source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L623-L637) · native range starts at 623.

<a id="api-0d7c10b07a0a60a5"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply_native`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply_native {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) (z : ↑(Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))))) : ((ofInjectiveResolution X' I).extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (injectiveCyclesCokernelSourceMap I g n)) z) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) (n + 1))) (((ofInjectiveResolution X I).extZeroCokernelIsoHomology n).addCommGroupIsoToAddEquiv z)
```

**Native source docstring:**

Source naturality of the cokernel/homology comparison, stated with the
native acyclic-resolution comparison.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L606-L620) · native range starts at 606.

<a id="api-11ba005502f88dd9"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_apply {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) (z : ↑(Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))))) : (injectiveExtZeroCokernelIsoHomology I X' n).addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (injectiveCyclesCokernelSourceMap I g n)) z) = (ConcreteCategory.hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) (n + 1))) ((injectiveExtZeroCokernelIsoHomology I X n).addCommGroupIsoToAddEquiv z)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L589-L603) · native range starts at 589.

<a id="api-7882ee6f022c8fd6"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (ofInjectiveResolution X' I).extZeroComplex (n + 1) ⟶ Z) : CategoryStruct.comp (injectiveCyclesCokernelSourceMap I g n) (CategoryStruct.comp (injectiveExtZeroCokernelIsoHomology I X' n).hom h) = CategoryStruct.comp (injectiveExtZeroCokernelIsoHomology I X n).hom (CategoryStruct.comp (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) (n + 1)) h)
```

**Native source docstring:**

The canonical dimension-shift cokernel/homology comparison for a fixed
injective resolution is contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L512-L512) · native range starts at 512.

<a id="api-29980836d794d675"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology_hom_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : CategoryStruct.comp (injectiveCyclesCokernelSourceMap I g n) (injectiveExtZeroCokernelIsoHomology I X' n).hom = CategoryStruct.comp (injectiveExtZeroCokernelIsoHomology I X n).hom (HomologicalComplex.homologyMap (injectiveExtZeroComplexSourceMap I g) (n + 1))
```

**Native source docstring:**

The canonical dimension-shift cokernel/homology comparison for a fixed
injective resolution is contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L510-L587) · native range starts at 510.

<a id="api-6e9857a9e0b32fe8"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveCyclesCokernelSourceMap_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveCyclesCokernelSourceMap_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) {Z : AddCommGrpCat} (h : Limits.cokernel ((extFunctorObj X' 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))) ⟶ Z) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))) (CategoryStruct.comp (injectiveCyclesCokernelSourceMap I g n) h) = CategoryStruct.comp (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex (n + 1))) (CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X' 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L497-L497) · native range starts at 497.

<a id="api-8287054a5ba88dbb"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveCyclesCokernelSourceMap`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveCyclesCokernelSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))) (injectiveCyclesCokernelSourceMap I g n) = CategoryStruct.comp (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex (n + 1))) (Limits.cokernel.π ((extFunctorObj X' 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L497-L507) · native range starts at 497.

<a id="api-6e34f9a0463bd247"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveExtZeroCokernelIsoHomology_hom_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveExtZeroCokernelIsoHomology_hom_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X : C} (I : InjectiveResolution A) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (ofInjectiveResolution X I).extZeroComplex (n + 1) ⟶ Z) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))) (CategoryStruct.comp (injectiveExtZeroCokernelIsoHomology I X n).hom h) = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso (n + 1)).inv (CategoryStruct.comp (HomologicalComplex.homologyπ (ofInjectiveResolution X I).extZeroComplex (n + 1)) h)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L484-L484) · native range starts at 484.

<a id="api-ce838a84816ebbc3"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveExtZeroCokernelIsoHomology_hom`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.cokernelπ_injectiveExtZeroCokernelIsoHomology_hom {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X : C} (I : InjectiveResolution A) (n : ℕ) : CategoryStruct.comp (Limits.cokernel.π ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))) (injectiveExtZeroCokernelIsoHomology I X n).hom = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso (n + 1)).inv (HomologicalComplex.homologyπ (ofInjectiveResolution X I).extZeroComplex (n + 1))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L484-L494) · native range starts at 484.

<a id="api-2ce6458aa68d458b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCokernelIsoHomology {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A : C} (I : InjectiveResolution A) (X : C) (n : ℕ) : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))) ≅ HomologicalComplex.homology (ofInjectiveResolution X I).extZeroComplex (n + 1)
```

**Native source docstring:**

The canonical dimension-shift cokernel/homology comparison for a fixed
injective resolution.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L472-L481) · native range starts at 472.

<a id="api-4fc42cd48989461f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_inv_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_inv_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.cycles (ofInjectiveResolution X' I).extZeroComplex n ⟶ Z) : CategoryStruct.comp (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex n)) (CategoryStruct.comp ((ofInjectiveResolution X' I).extZeroCyclesIso n).inv h) = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso n).inv (CategoryStruct.comp (HomologicalComplex.cyclesMap (injectiveExtZeroComplexSourceMap I g) n) h)
```

**Native source docstring:**

Inverse form of source naturality for the degree-zero Ext/cycles
comparison.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L457-L457) · native range starts at 457.

<a id="api-3d2519d55e7a0b22"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_inv_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_inv_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : CategoryStruct.comp (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex n)) ((ofInjectiveResolution X' I).extZeroCyclesIso n).inv = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso n).inv (HomologicalComplex.cyclesMap (injectiveExtZeroComplexSourceMap I g) n)
```

**Native source docstring:**

Inverse form of source naturality for the degree-zero Ext/cycles
comparison.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L455-L470) · native range starts at 455.

<a id="api-8435f6342f4fdc61"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_hom_source_naturality_assoc`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_hom_source_naturality_assoc {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) {Z : AddCommGrpCat} (h : (extFunctorObj X' 0).obj (HomologicalComplex.cycles (ofInjectiveResolution X' I).cocomplex n) ⟶ Z) : CategoryStruct.comp (HomologicalComplex.cyclesMap (injectiveExtZeroComplexSourceMap I g) n) (CategoryStruct.comp ((ofInjectiveResolution X' I).extZeroCyclesIso n).hom h) = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso n).hom (CategoryStruct.comp (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex n)) h)
```

**Native source docstring:**

The degree-zero Ext/cycles comparison for a fixed injective resolution is
contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L394-L394) · native range starts at 394.

<a id="api-3edee1be5cccf246"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_hom_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroCyclesIso_hom_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : CategoryStruct.comp (HomologicalComplex.cyclesMap (injectiveExtZeroComplexSourceMap I g) n) ((ofInjectiveResolution X' I).extZeroCyclesIso n).hom = CategoryStruct.comp ((ofInjectiveResolution X I).extZeroCyclesIso n).hom (extSourceMap g 0 (HomologicalComplex.cycles I.cocomplex n))
```

**Native source docstring:**

The degree-zero Ext/cycles comparison for a fixed injective resolution is
contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L392-L452) · native range starts at 392.

<a id="api-50c69630269067a2"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso_inv_source_naturality_apply_native`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso_inv_source_naturality_apply_native {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) (x : Ext X (HomologicalComplex.cycles I.cocomplex n) 1) [Subsingleton (Ext X ((ofInjectiveResolution X I).cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X' ((ofInjectiveResolution X I).cyclesShortComplex n).X₂ 1)] [Subsingleton (Ext X' ((ofInjectiveResolution X' I).cyclesShortComplex n).X₂ 1)] : ((ofInjectiveResolution X' I).cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm ((mk₀ g).comp x ⋯) = (ConcreteCategory.hom (injectiveCyclesCokernelSourceMap I g n)) (((ofInjectiveResolution X I).cyclesCokernelIso n).addCommGroupIsoToAddEquiv.symm x)
```

**Native source docstring:**

Source naturality of the inverse cycle-cokernel comparison, stated with
the native acyclic-resolution comparison.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L364-L389) · native range starts at 364.

<a id="api-66b0913c7ddf150c"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso_inv_source_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso_inv_source_naturality_apply {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) (x : Ext X (HomologicalComplex.cycles I.cocomplex n) 1) : (injectiveCyclesCokernelIso I X' n).addCommGroupIsoToAddEquiv.symm ((mk₀ g).comp x ⋯) = (ConcreteCategory.hom (injectiveCyclesCokernelSourceMap I g n)) ((injectiveCyclesCokernelIso I X n).addCommGroupIsoToAddEquiv.symm x)
```

**Native source docstring:**

The inverse cycle-cokernel comparison for a fixed injective resolution is
contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L315-L361) · native range starts at 315.

<a id="api-7cf75fd847e73957"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelSourceMap`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n : ℕ) : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))) ⟶ Limits.cokernel ((extFunctorObj X' 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1)))
```

**Native source docstring:**

Precomposition on the dimension-shift cokernels of a fixed injective
resolution.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L302-L312) · native range starts at 302.

<a id="api-a007612b672f0d8a"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesCokernelIso {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A : C} (I : InjectiveResolution A) (X : C) (n : ℕ) : Limits.cokernel ((extFunctorObj X 0).map (HomologicalComplex.toCycles I.cocomplex n (n + 1))) ≅ ↧(Ext X (HomologicalComplex.cycles I.cocomplex n) 1)
```

**Native source docstring:**

The cycle-cokernel comparison for a fixed injective resolution, with its
degree-one acyclicity witness encapsulated.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L287-L300) · native range starts at 287.

<a id="api-6816d877752220e9"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.covariantCokernelIso_source_naturality_apply`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.covariantCokernelIso_source_naturality_apply {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) {S : ShortComplex C} (hS : S.ShortExact) [Subsingleton (Ext X S.X₂ 1)] [Subsingleton (Ext X' S.X₂ 1)] (z : ↑(Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X ⋯)))) : (covariantCokernelIso hS X').addCommGroupIsoToAddEquiv ((ConcreteCategory.hom (covariantCokernelSourceMap g)) z) = (mk₀ g).comp ((covariantCokernelIso hS X).addCommGroupIsoToAddEquiv z) ⋯
```

**Native source docstring:**

The connecting isomorphism from a degree-zero cokernel to degree-one Ext
is contravariantly natural in the source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L231-L285) · native range starts at 231.

<a id="api-d90327664af7fa92"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesDimensionShiftIterate_symm_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesDimensionShiftIterate_symm_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n q : ℕ) (hq : 0 < q) (x : Ext X (HomologicalComplex.cycles I.cocomplex 0) (n + q)) : ((ofInjectiveResolution X' I).cyclesDimensionShiftIterate n q hq).symm ((mk₀ g).comp x ⋯) = (mk₀ g).comp (((ofInjectiveResolution X I).cyclesDimensionShiftIterate n q hq).symm x) ⋯
```

**Native source docstring:**

The inverse iterated cycle dimension shift for a fixed injective
resolution is contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L211-L227) · native range starts at 211.

<a id="api-54fbe13032dfa30b"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesDimensionShiftIterate_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveCyclesDimensionShiftIterate_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) (n q : ℕ) (hq : 0 < q) (x : Ext X (HomologicalComplex.cycles I.cocomplex n) q) : ((ofInjectiveResolution X' I).cyclesDimensionShiftIterate n q hq) ((mk₀ g).comp x ⋯) = (mk₀ g).comp (((ofInjectiveResolution X I).cyclesDimensionShiftIterate n q hq) x) ⋯
```

**Native source docstring:**

The iterated cycle dimension shift for a fixed injective resolution is
contravariantly natural in its source.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L147-L208) · native range starts at 147.

<a id="api-87113fc96bae3d8f"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.covariantDimensionShift_source_naturality`

```lean
theorem CategoryTheory.Abelian.Ext.AcyclicResolution.covariantDimensionShift_source_naturality {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext X S.X₂ n)] [Subsingleton (Ext X S.X₂ (n + 1))] [Subsingleton (Ext X' S.X₂ n)] [Subsingleton (Ext X' S.X₂ (n + 1))] (x : Ext X S.X₃ n) : (covariantDimensionShift hS X' n) ((mk₀ g).comp x ⋯) = (mk₀ g).comp ((covariantDimensionShift hS X n) x) ⋯
```

**Native source docstring:**

The covariant connecting equivalence is contravariantly natural in the
source object.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L123-L137) · native range starts at 123.

<a id="api-86d935a34560b430"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.covariantCokernelSourceMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.covariantCokernelSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) {S : ShortComplex C} : Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X ⋯)) ⟶ Limits.cokernel (AddCommGrpCat.ofHom ((mk₀ S.g).postcomp X' ⋯))
```

**Native source docstring:**

Precomposition on the cokernels used in the degree-one dimension shift.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L106-L121) · native range starts at 106.

<a id="api-1a9c5f5626d27bb6"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveHomComplexSourceMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveHomComplexSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) : (ofInjectiveResolution X I).homComplex ⟶ (ofInjectiveResolution X' I).homComplex
```

**Native source docstring:**

Precomposition on the additive-coyoneda complexes of a fixed injective
resolution.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L97-L104) · native range starts at 97.

<a id="api-dcfd76e4e237059e"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexSourceMap`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtZeroComplexSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X) : (ofInjectiveResolution X I).extZeroComplex ⟶ (ofInjectiveResolution X' I).extZeroComplex
```

**Native source docstring:**

Precomposition on the degree-zero Ext complexes of a fixed injective
resolution.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L83-L95) · native range starts at 83.

<a id="api-0eeaa4de128a7ecd"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.extSourceMap`

```lean
noncomputable abbrev CategoryTheory.Abelian.Ext.AcyclicResolution.extSourceMap {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] {X X' : C} (g : X' ⟶ X) (n : ℕ) (Y : C) : (extFunctorObj X n).obj Y ⟶ (extFunctorObj X' n).obj Y
```

**Native source docstring:**

Precomposition on Ext, with the source and target functors exposed in a
form convenient for exact cokernel constructions.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L77-L81) · native range starts at 77.

<a id="api-f27192c7300da9e8"></a>

### `CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution`

```lean
noncomputable def CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution {C : Type u} [Category.{v, u} C] [Abelian C] [HasExt C] (X : C) {Z : C} (I : InjectiveResolution Z) : AcyclicResolution X Z
```

**Native source docstring:**

Every injective resolution is acyclic for `Ext X -`.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L57-L65) · native range starts at 57.

<a id="api-fa20d5bb759b86cb"></a>

### `CategoryTheory.Functor.mapInjectiveResolution`

```lean
noncomputable def CategoryTheory.Functor.mapInjectiveResolution {C : Type u} [Category.{v, u} C] [Limits.HasZeroObject C] [Preadditive C] {D : Type u} [Category.{v, u} D] [Limits.HasZeroObject D] [Preadditive D] [CategoryWithHomology D] (F : Functor C D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology] {Z : C} (I : InjectiveResolution Z) : InjectiveResolution (F.obj Z)
```

**Native source docstring:**

The injective dual of `mapProjectiveResolution`.

[Frozen source](../SheafCohomology/InjectiveResolutionNaturality.lean#L38-L49) · native range starts at 38.

## `SheafCohomology.LocalCohomology`

Scope: subject module.

<a id="api-cf0990c858312f22"></a>

### `TopCat.Sheaf.toSheafifiedLocalCohomology_app`

```lean
theorem TopCat.Sheaf.toSheafifiedLocalCohomology_app {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (q : ℕ) (F : Sheaf AddCommGrpCat X) : (toSheafifiedLocalCohomology f q).app F = (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology ↑Y) AddCommGrpCat).unit.app (localCohomologyPresheaf f F q)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L118-L124) · native range starts at 118.

<a id="api-5cd59ad616abd326"></a>

### `TopCat.Sheaf.toSheafifiedLocalCohomology`

```lean
noncomputable def TopCat.Sheaf.toSheafifiedLocalCohomology {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (q : ℕ) : localCohomologyPresheafFunctor f q ⟶ (sheafifiedLocalCohomologyFunctor f q).comp (forget AddCommGrpCat Y)
```

**Native source docstring:**

The canonical map from the local-cohomology presheaf to the underlying
presheaf of its sheafification.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L108-L116) · native range starts at 108.

<a id="api-2b9006949e9470ab"></a>

### `TopCat.Sheaf.sheafifiedLocalCohomology`

```lean
noncomputable abbrev TopCat.Sheaf.sheafifiedLocalCohomology {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (F : Sheaf AddCommGrpCat X) (q : ℕ) : Sheaf AddCommGrpCat Y
```

**Native source docstring:**

The sheafified local cohomology of `F` along `f` in degree `q`.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L102-L106) · native range starts at 102.

<a id="api-f1a443b0aaa1c844"></a>

### `TopCat.Sheaf.sheafifiedLocalCohomologyFunctor`

```lean
noncomputable def TopCat.Sheaf.sheafifiedLocalCohomologyFunctor {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (q : ℕ) : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Sheaf AddCommGrpCat Y)
```

**Native source docstring:**

Sheafification of the local-cohomology presheaf, functorial in the
coefficient sheaf.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L91-L100) · native range starts at 91.

<a id="api-d60c1fd57b72499a"></a>

### `TopCat.Sheaf.localCohomologyPresheafFunctor_map_app`

```lean
theorem TopCat.Sheaf.localCohomologyPresheafFunctor_map_app {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) {F G : Sheaf AddCommGrpCat X} (a : F ⟶ G) (U : TopologicalSpace.Opens ↑Y) : ((localCohomologyPresheafFunctor f q).map a).app (Opposite.op U) = ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op ((TopologicalSpace.Opens.map f).obj U))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L79-L86) · native range starts at 79.

<a id="api-4d6cfe3c7c651288"></a>

### `TopCat.Sheaf.localCohomologyPresheaf_map`

```lean
theorem TopCat.Sheaf.localCohomologyPresheaf_map {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) (q : ℕ) {U V : TopologicalSpace.Opens ↑Y} (i : U ⟶ V) : (localCohomologyPresheaf f F q).map i.op = ((have this := F; this).cohomologyPresheaf q).map ((TopologicalSpace.Opens.map f).map i).op
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L69-L77) · native range starts at 69.

<a id="api-3d2c904d85683703"></a>

### `TopCat.Sheaf.localCohomologyPresheaf_obj`

```lean
theorem TopCat.Sheaf.localCohomologyPresheaf_obj {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) (q : ℕ) (U : TopologicalSpace.Opens ↑Y) : (localCohomologyPresheaf f F q).obj (Opposite.op U) = (have this := F; this).H' q ((TopologicalSpace.Opens.map f).obj U)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L60-L67) · native range starts at 60.

<a id="api-79414bcde08412ab"></a>

### `TopCat.Sheaf.localCohomologyPresheaf`

```lean
noncomputable abbrev TopCat.Sheaf.localCohomologyPresheaf {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (F : Sheaf AddCommGrpCat X) (q : ℕ) : Presheaf AddCommGrpCat Y
```

**Native source docstring:**

The local-cohomology presheaf of `F` along `f` in degree `q`.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L54-L58) · native range starts at 54.

<a id="api-8d49f3ba032903a2"></a>

### `TopCat.Sheaf.localCohomologyPresheafFunctor`

```lean
noncomputable def TopCat.Sheaf.localCohomologyPresheafFunctor {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) : CategoryTheory.Functor (Sheaf AddCommGrpCat X) (Presheaf AddCommGrpCat Y)
```

**Native source docstring:**

The presheaf on `Y` whose value on `U` is the Ext-based local cohomology
of a sheaf on `X` over `f ⁻¹ U`, functorial in the coefficient sheaf.

[Frozen source](../SheafCohomology/LocalCohomology.lean#L44-L52) · native range starts at 44.

## `SheafCohomology.LocalCohomologyFilteredColimit`

Scope: subject module.

<a id="api-efe32c838856709f"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport_stage_assoc`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport_stage_assoc {X₀ : TopCat} (U₀ : TopologicalSpace.Opens ↑X₀) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X₀) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X₀).over U₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)) (n : ℕ) (i : I) [CategoryTheory.Limits.HasColimit F] {Z : AddCommGrpCat} (h : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↥U₀) n).obj (U₀.sheafEquivOver.functor.obj ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).obj (CategoryTheory.Limits.colimit F))) ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (F.comp ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X₀) n).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑X₀)ᵒᵖ AddCommGrpCat).obj (Opposite.op U₀)))) i) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft (cohomologyPresheafEvaluationIsoHSubspace U₀ n).hom)) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).comp (U₀.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↥U₀) n)))) h)) = CategoryTheory.CategoryStruct.comp ((cohomologyPresheafEvaluationIsoHSubspace U₀ n).hom.app (F.obj i)) (CategoryTheory.CategoryStruct.comp ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↥U₀) n).map (U₀.sheafEquivOver.functor.map ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).map (CategoryTheory.Limits.colimit.ι F i)))) h)
```

**Native source docstring:**

On every filtered stage, the transported compact-open comparison is
literally the cohomology map induced by that stage's canonical map to the
colimit, after the fixed open-subspace comparison at the source stage.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L347-L347) · native range starts at 347.

<a id="api-cfd232b4ddcb8e0a"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport_stage`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport_stage {X₀ : TopCat} (U₀ : TopologicalSpace.Opens ↑X₀) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X₀) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X₀).over U₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)) (n : ℕ) (i : I) [CategoryTheory.Limits.HasColimit F] : have e := cohomologyPresheafEvaluationIsoHSubspace U₀ n; CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.ι (F.comp ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X₀) n).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑X₀)ᵒᵖ AddCommGrpCat).obj (Opposite.op U₀)))) i) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft e.hom)) (CategoryTheory.Limits.colimit.post F ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).comp (U₀.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑↧↥U₀) n))))) = CategoryTheory.CategoryStruct.comp (e.hom.app (F.obj i)) (((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).comp (U₀.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑↧↥U₀) n))).map (CategoryTheory.Limits.colimit.ι F i))
```

**Native source docstring:**

On every filtered stage, the transported compact-open comparison is
literally the cohomology map induced by that stage's canonical map to the
colimit, after the fixed open-subspace comparison at the source stage.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L344-L369) · native range starts at 344.

<a id="api-a4953006210aed11"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_colimitPost_transport {X₀ : TopCat} (U₀ : TopologicalSpace.Opens ↑X₀) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X₀) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X₀).over U₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat)] {I : Type} [CategoryTheory.SmallCategory I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)) (n : ℕ) [CategoryTheory.Limits.HasColimit F] : have e := cohomologyPresheafEvaluationIsoHSubspace U₀ n; CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft e.hom)) (CategoryTheory.Limits.colimit.post F ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U₀).comp (U₀.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑↧↥U₀) n)))) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X₀) n).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑X₀)ᵒᵖ AddCommGrpCat).obj (Opposite.op U₀)))) (e.hom.app (CategoryTheory.Limits.colimit F))
```

**Native source docstring:**

The transported compact-open comparison is the canonical comparison for
cohomology on the topological subspace, with no choice of an unrelated
isomorphism between the same endpoints.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L317-L340) · native range starts at 317.

<a id="api-e02223fb0a1dd71b"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_preservesColimit`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluation_preservesColimit {X₀ : TopCat} (U₀ : TopologicalSpace.Opens ↑X₀) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X₀) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X₀).over U₀).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X₀).over U₀) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U₀) AddCommGrpCat)] [PrespectralSpace ↥U₀] [CompactSpace ↥U₀] [QuasiSeparatedSpace ↥U₀] {I : Type} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X₀) AddCommGrpCat)) (n : ℕ) : CategoryTheory.Limits.PreservesColimit F ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X₀) n).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑X₀)ᵒᵖ AddCommGrpCat).obj (Opposite.op U₀)))
```

**Native source docstring:**

On a compact prespectral quasi-separated open, evaluation of the
cohomology presheaf preserves a same-small-universe filtered colimit.  The
proof transports first to the open over-site and then to the corresponding
topological subspace, where the accepted filtered-colimit theorem applies.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L288-L313) · native range starts at 288.

<a id="api-e31ecbd4bb10a834"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluationIsoHSubspace`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.cohomologyPresheafEvaluationIsoHSubspace {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U) AddCommGrpCat)] (n : ℕ) : (CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) n).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑X)ᵒᵖ AddCommGrpCat).obj (Opposite.op U)) ≅ (CategoryTheory.Sheaf.OpenCohomology.restrictToOver U).comp (U.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑↧↥U) n))
```

**Native source docstring:**

Evaluation of the cohomology presheaf on an open agrees naturally with
cohomology on the corresponding topological subspace.  This is the composite
of the open-over-site comparison and the dense-subsite equivalence.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L244-L257) · native range starts at 244.

<a id="api-624cc3f53e061aa6"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.functorHOverIsoFunctorHSubspace`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.functorHOverIsoFunctorHSubspace {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U) AddCommGrpCat)] (n : ℕ) : CategoryTheory.Sheaf.functorH ((Opens.grothendieckTopology ↑X).over U) n ≅ U.sheafEquivOver.functor.comp (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology ↑↧↥U) n)
```

**Native source docstring:**

Cohomology on the open over-site and on the corresponding topological
subspace agree as functors of the coefficient sheaf.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L227-L239) · native range starts at 227.

<a id="api-be1638d822725cbc"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.HOverEquivHSubspace_naturality`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.HOverEquivHSubspace_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U) AddCommGrpCat)] {G G' : CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat} (f : G ⟶ G') (n : ℕ) (x : G.H n) : (CategoryTheory.Sheaf.H.map (U.sheafEquivOver.functor.map f) n) ((HOverEquivHSubspace U G n) x) = (HOverEquivHSubspace U G' n) ((CategoryTheory.Sheaf.H.map f n) x)
```

**Native source docstring:**

The open-over-site/open-subspace cohomology equivalence is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L138-L214) · native range starts at 138.

<a id="api-55cd7e9a8af3cb56"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.HOverEquivHSubspace`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.HOverEquivHSubspace {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑↧↥U) AddCommGrpCat)] (G : CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat) (n : ℕ) : G.H n ≃+ (U.sheafEquivOver.functor.obj G).H n
```

**Native source docstring:**

Cohomology on an open over-site agrees additively with cohomology after
transport to the corresponding topological subspace.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L96-L125) · native range starts at 96.

<a id="api-80aa51077ce0e1f7"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.overConstantIso`

```lean
noncomputable def SheafCohomology.HigherDirectImageFilteredColimit.overConstantIso {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] : U.sheafEquivOver.functor.obj ((CategoryTheory.constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj ↧(ULift.{u, 0} ℤ)) ≅ (CategoryTheory.constantSheaf (Opens.grothendieckTopology ↑↧↥U) AddCommGrpCat).obj ↧(ULift.{u, 0} ℤ)
```

**Native source docstring:**

The dense-subsite equivalence from the open over-site to the topology on
the open carries the constant integral sheaf to the constant integral sheaf.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L76-L92) · native range starts at 76.

<a id="api-020ae9078e302f55"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.restrictToOver_preservesColimits`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.restrictToOver_preservesColimits {X : TopCat} (U : TopologicalSpace.Opens ↑X) : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (CategoryTheory.Sheaf.OpenCohomology.restrictToOver U)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/LocalCohomologyFilteredColimit.lean#L36-L55) · native range starts at 36.

## `SheafCohomology.OpenBaseChange`

Scope: subject module.

<a id="api-68348322375d6389"></a>

### `TopCat.Sheaf.OpenBaseChange.baseChangeIso_hom_app_comp_counit`

```lean
theorem TopCat.Sheaf.OpenBaseChange.baseChangeIso_hom_app_comp_counit {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) (F : Sheaf (Type v) X) : CategoryTheory.CategoryStruct.comp ((pullback (Type v) (preimageMap f V)).map ((baseChangeIso f V).hom.app F)) ((pullbackPushforwardAdjunction (Type v) (preimageMap f V)).counit.app ((pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion').obj F)) = CategoryTheory.CategoryStruct.comp ((pullbackSquareIso f V).hom.app ((pushforward (Type v) f).obj F)) ((pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion').map ((pullbackPushforwardAdjunction (Type v) f).counit.app F))
```

**Native source docstring:**

The mate identification as the literal counit/naturality equation.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L471-L492) · native range starts at 471.

<a id="api-bb69109c04dadd2f"></a>

### `TopCat.Sheaf.OpenBaseChange.baseChangeSquare_inv_mate`

```lean
theorem TopCat.Sheaf.OpenBaseChange.baseChangeSquare_inv_mate {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (CategoryTheory.mateEquiv (pullbackPushforwardAdjunction (Type v) f) (pullbackPushforwardAdjunction (Type v) (preimageMap f V))).symm (baseChangeSquare f V) = pullbackSquare f V
```

**Native source docstring:**

The inverse mate of direct-image open base change is the geometric square.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L457-L469) · native range starts at 457.

<a id="api-df0afd610ab085c2"></a>

### `TopCat.Sheaf.OpenBaseChange.pullbackSquare_mate`

```lean
theorem TopCat.Sheaf.OpenBaseChange.pullbackSquare_mate {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (CategoryTheory.mateEquiv (pullbackPushforwardAdjunction (Type v) f) (pullbackPushforwardAdjunction (Type v) (preimageMap f V))) (pullbackSquare f V) = baseChangeSquare f V
```

**Native source docstring:**

The mate of the geometric inverse-image square is direct-image base change.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L428-L455) · native range starts at 428.

<a id="api-857a24d321b7771b"></a>

### `TopCat.Sheaf.OpenBaseChange.baseChangeSquare`

```lean
noncomputable def TopCat.Sheaf.OpenBaseChange.baseChangeSquare {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : CategoryTheory.TwoSquare (pushforward (Type v) f) (pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion') (pullback (Type v) V.inclusion') (pushforward (Type v) (preimageMap f V))
```

**Native source docstring:**

Direct-image open base change packaged as a `TwoSquare`.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L243-L250) · native range starts at 243.

<a id="api-f6571e7a427256da"></a>

### `TopCat.Sheaf.OpenBaseChange.pullbackSquare`

```lean
noncomputable def TopCat.Sheaf.OpenBaseChange.pullbackSquare {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : CategoryTheory.TwoSquare (pullback (Type v) V.inclusion') (pullback (Type v) f) (pullback (Type v) (preimageMap f V)) (pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion')
```

**Native source docstring:**

The inverse-image comparison packaged as a `TwoSquare`.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L234-L241) · native range starts at 234.

<a id="api-6263040430290e62"></a>

### `TopCat.Sheaf.OpenBaseChange.pullbackSquareIso`

```lean
noncomputable def TopCat.Sheaf.OpenBaseChange.pullbackSquareIso {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (pullback (Type v) V.inclusion').comp (pullback (Type v) (preimageMap f V)) ≅ (pullback (Type v) f).comp (pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion')
```

**Native source docstring:**

The inverse-image comparison induced by composition and the commuting square.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L217-L232) · native range starts at 217.

<a id="api-66ce8d30f2905217"></a>

### `TopCat.Sheaf.OpenBaseChange.baseChangeIso`

```lean
noncomputable def TopCat.Sheaf.OpenBaseChange.baseChangeIso {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (pushforward (Type v) f).comp (pullback (Type v) V.inclusion') ≅ (pullback (Type v) ((TopologicalSpace.Opens.map f).obj V).inclusion').comp (pushforward (Type v) (preimageMap f V))
```

**Native source docstring:**

Direct-image base change along an open inverse-image square.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L163-L204) · native range starts at 163.

<a id="api-eab2eed0606c4896"></a>

### `TopCat.Sheaf.OpenBaseChange.preimageOpensIso`

```lean
def TopCat.Sheaf.OpenBaseChange.preimageOpensIso {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : ⋯.functor.comp (TopologicalSpace.Opens.map f) ≅ (TopologicalSpace.Opens.map (preimageMap f V)).comp ⋯.functor
```

**Native source docstring:**

The canonical comparison of functors on opens for the inverse-image square.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L127-L148) · native range starts at 127.

<a id="api-6d2fa85d3f0ca2bb"></a>

### `TopCat.Sheaf.OpenBaseChange.preimageMap_comp_inclusion`

```lean
theorem TopCat.Sheaf.OpenBaseChange.preimageMap_comp_inclusion {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : CategoryTheory.CategoryStruct.comp (preimageMap f V) V.inclusion' = CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).obj V).inclusion' f
```

**Native source docstring:**

The inverse-image open square commutes literally in `TopCat`.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L119-L125) · native range starts at 119.

<a id="api-ec8042c00957f9f3"></a>

### `TopCat.Sheaf.OpenBaseChange.preimageMap`

```lean
def TopCat.Sheaf.OpenBaseChange.preimageMap {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (TopologicalSpace.Opens.toTopCat X).obj ((TopologicalSpace.Opens.map f).obj V) ⟶ (TopologicalSpace.Opens.toTopCat Y).obj V
```

**Native source docstring:**

The canonical map from the inverse-image open subspace `f⁻¹(V)` to `V`.

[Frozen source](../SheafCohomology/OpenBaseChange.lean#L111-L117) · native range starts at 111.

## `SheafCohomology.OpenCohomology`

Scope: subject module.

<a id="api-e76e6f850779f34d"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver_map`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver_map {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [globalSheafify : HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] [overUExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [overVExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat)] [globalExt : HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) (x : ↑(G.H' n U)) : (HOverMap i G n) ((HPrimeEquivHOver U G n) x) = (HPrimeEquivHOver V G n) ((ConcreteCategory.hom (((cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) n).obj G).map i.op)) x)
```

**Native source docstring:**

Under `HPrimeEquivHOver`, the intrinsic over-site restriction agrees with
the restriction map of `Sheaf.cohomologyPresheafFunctor`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L1162-L1247) · native range starts at 1162.

<a id="api-d382b0217d0a46b5"></a>

### `CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor_map`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor_map {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) : globalCohomologySourceFunctor.map i = CategoryStruct.comp (cohomologySourceIsoOverConstantSource V).hom (CategoryStruct.comp (overConstantSourceMap i ↧(ULift.{u, 0} ℤ)) (cohomologySourceIsoOverConstantSource U).inv)
```

**Native source docstring:**

The sheafified free-Yoneda source map along `V ⟶ U` is the canonical
over-site source map transported through the two representing isomorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L901-L1159) · native range starts at 901.

<a id="api-51213948e7135247"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overConstantSourceMap_homEquiv`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.overConstantSourceMap_homEquiv {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) (M : AddCommGrpCat) : ((Adjunction.ofIsRightAdjoint (restrictToOver V)).homEquiv ((constantSheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat).obj M) ((restrictToOver U).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M))) (overConstantSourceMap i M) = CategoryStruct.comp (constantRestrictIso i M).hom (CategoryStruct.comp ((inclusionRestrict i).map (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M) ((restrictToOver U).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M))) (CategoryStruct.id ((restrictToOver U).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M))))) ((restrictToOverCompIso i).hom.app ((restrictToOver U).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M))))
```

**Native source docstring:**

The adjunction mate of `overConstantSourceMap`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L778-L894) · native range starts at 778.

<a id="api-c042b419b98d4d8e"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overConstantSourceMap`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overConstantSourceMap {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) (M : AddCommGrpCat) : (restrictToOver V).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat).obj M) ⟶ (restrictToOver U).leftAdjoint.obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M)
```

**Native source docstring:**

The map between the two ambient cohomology source objects induced by an
inclusion `V ⟶ U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L757-L771) · native range starts at 757.

<a id="api-826b928d921cad7c"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overLeftAdjointCompIso`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overLeftAdjointCompIso {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) : (restrictToOver V).leftAdjoint ≅ (inclusionRestrict i).leftAdjoint.comp (restrictToOver U).leftAdjoint
```

**Native source docstring:**

The canonical comparison between direct extension from `V` and extension
first to `U` and then to `X`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L746-L755) · native range starts at 746.

<a id="api-9f321929ab194ada"></a>

### `CategoryTheory.Sheaf.OpenCohomology.sectionsRestrict`

```lean
abbrev CategoryTheory.Sheaf.OpenCohomology.sectionsRestrict {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) : sectionsAtType U ⟶ sectionsAtType V
```

**Native source docstring:**

Restriction of sections from `U` to `V`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L737-L744) · native range starts at 737.

<a id="api-1a4938eec7b28fa1"></a>

### `CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor`

```lean
noncomputable abbrev CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor {X : TopCat} : Functor (TopologicalSpace.Opens ↑X) (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)
```

**Native source docstring:**

The sheafified free-Yoneda cohomology source, functorial in the open.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L727-L735) · native range starts at 727.

<a id="api-57d4e8e7736ddb5e"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HOverMap_comp`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.HOverMap_comp {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] [overUExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [overVExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat)] {W : TopologicalSpace.Opens ↑X} (j : W ⟶ V) [overWSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over W) AddCommGrpCat] [overWLocallyBijective : ((Opens.grothendieckTopology ↑X).over W).WEqualsLocallyBijective AddCommGrpCat] [overWSheafCompose : ((Opens.grothendieckTopology ↑X).over W).HasSheafCompose (forget AddCommGrpCat)] [overWExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over W) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : HOverMap (CategoryStruct.comp j i) G n = (HOverMap j G n).comp (HOverMap i G n)
```

**Native source docstring:**

Intrinsic over-site cohomology restrictions compose contravariantly.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L687-L721) · native range starts at 687.

<a id="api-90d6511a26752294"></a>

### `CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso_comp`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso_comp {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) {W : TopologicalSpace.Opens ↑X} (j : W ⟶ V) (M : AddCommGrpCat) : (constantRestrictIso (CategoryStruct.comp j i) M).hom = CategoryStruct.comp (constantRestrictIso j M).hom (CategoryStruct.comp ((inclusionRestrict j).map (constantRestrictIso i M).hom) (((Opens.grothendieckTopology ↑X).overMapPullbackComp AddCommGrpCat j i).hom.app ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M)))
```

**Native source docstring:**

The constant-sheaf transport is compatible with composition of open
inclusions.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L654-L683) · native range starts at 654.

<a id="api-a85ca18d4cae62c5"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso_comp`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso_comp {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) {W : TopologicalSpace.Opens ↑X} (j : W ⟶ V) (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : ((restrictToOverCompIso (CategoryStruct.comp j i)).app G).hom = CategoryStruct.comp (((Opens.grothendieckTopology ↑X).overMapPullbackComp AddCommGrpCat j i).inv.app (G.over U)) (CategoryStruct.comp ((inclusionRestrict j).map ((restrictToOverCompIso i).app G).hom) ((restrictToOverCompIso j).app G).hom)
```

**Native source docstring:**

The ambient restriction comparison is compatible with composition of
open inclusions.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L631-L646) · native range starts at 631.

<a id="api-18a40ad9fa1bc85c"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HOverMap_id`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.HOverMap_id {X : TopCat} {U : TopologicalSpace.Opens ↑X} [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overUExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : HOverMap (CategoryStruct.id U) G n = AddMonoidHom.id ((G.over U).H n)
```

**Native source docstring:**

The intrinsic over-site cohomology restriction is the identity for the
identity inclusion.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L588-L609) · native range starts at 588.

<a id="api-52236934574f5cb2"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso_id`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso_id {X : TopCat} {U : TopologicalSpace.Opens ↑X} (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : ((restrictToOverCompIso (CategoryStruct.id U)).app G).hom = ((Opens.grothendieckTopology ↑X).overMapPullbackId AddCommGrpCat U).hom.app (G.over U)
```

**Native source docstring:**

The ambient restriction comparison is compatible with the identity
inclusion.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L571-L584) · native range starts at 571.

<a id="api-310ae8a2562c9639"></a>

### `CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso_id`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso_id {X : TopCat} {U : TopologicalSpace.Opens ↑X} (M : AddCommGrpCat) : (constantRestrictIso (CategoryStruct.id U) M).hom = ((Opens.grothendieckTopology ↑X).overMapPullbackId AddCommGrpCat U).inv.app ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M)
```

**Native source docstring:**

The constant-sheaf transport is compatible with the identity inclusion.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L541-L565) · native range starts at 541.

<a id="api-848fd89de71eacad"></a>

### `CategoryTheory.Sheaf.OpenCohomology.toSheafify_constantRestrictIso`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.toSheafify_constantRestrictIso {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) (M : AddCommGrpCat) : CategoryStruct.comp (toSheafify ((Opens.grothendieckTopology ↑X).over V) ((Functor.const (Over V)ᵒᵖ).obj M)) (constantRestrictIso i M).hom.hom = CategoryStruct.comp ((Functor.constCompWhiskeringLeftIso (Over V)ᵒᵖ (Over.map i).op).inv.app M) ((Over.map i).op.whiskerLeft (toSheafify ((Opens.grothendieckTopology ↑X).over U) ((Functor.const (Over U)ᵒᵖ).obj M)))
```

**Native source docstring:**

The sheafification unit commutes with the constant-sheaf transport along
an inclusion of opens.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L519-L535) · native range starts at 519.

<a id="api-6ff9430853e0994c"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HOverMap`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.HOverMap {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] [overUExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [overVExt : HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : (G.over U).H n →+ (G.over V).H n
```

**Native source docstring:**

The intrinsic cohomology restriction along an inclusion of ambient opens,
obtained by applying the exact over-site restriction functor and transporting
the constant source and restricted coefficient sheaf through their canonical
isomorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L493-L512) · native range starts at 493.

<a id="api-03e551f8de4a4732"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) : (restrictToOver U).comp (inclusionRestrict i) ≅ restrictToOver V
```

**Native source docstring:**

Restricting first to `U` and then along `V ⟶ U` agrees naturally with
restricting directly to `V`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L476-L484) · native range starts at 476.

<a id="api-a224cad40d2a49a7"></a>

### `CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.constantRestrictIso {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) (M : AddCommGrpCat) : (constantSheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat).obj M ≅ (inclusionRestrict i).obj ((constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj M)
```

**Native source docstring:**

Restriction along `V ⟶ U` carries the constant sheaf on `J.over U` to
the constant sheaf on `J.over V`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L458-L474) · native range starts at 458.

<a id="api-77bfd32b4ce2966a"></a>

### `CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_preservesFiniteColimits`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_preservesFiniteColimits {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] : Limits.PreservesFiniteColimits (inclusionRestrict i)
```

**Native source docstring:**

Restriction along an inclusion of open over-sites preserves finite
colimits.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L449-L457) · native range starts at 449.

<a id="api-05ded577e08d4e26"></a>

### `CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_preservesEpimorphisms`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_preservesEpimorphisms {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] : (inclusionRestrict i).PreservesEpimorphisms
```

**Native source docstring:**

Restriction along an inclusion of open over-sites preserves
epimorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L443-L447) · native range starts at 443.

<a id="api-a0e6ec4d7b7ba8c2"></a>

### `CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_epi`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict_epi {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) [overUSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [overVSheafify : HasSheafify ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat] [overULocallyBijective : ((Opens.grothendieckTopology ↑X).over U).WEqualsLocallyBijective AddCommGrpCat] [overUSheafCompose : ((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [overVLocallyBijective : ((Opens.grothendieckTopology ↑X).over V).WEqualsLocallyBijective AddCommGrpCat] [overVSheafCompose : ((Opens.grothendieckTopology ↑X).over V).HasSheafCompose (forget AddCommGrpCat)] {F G : Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat} (a : F ⟶ G) [Epi a] : Epi ((inclusionRestrict i).map a)
```

**Native source docstring:**

Restriction along an inclusion of open over-sites preserves
epimorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L423-L441) · native range starts at 423.

<a id="api-8ab7aac0cd7c64f7"></a>

### `CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict`

```lean
abbrev CategoryTheory.Sheaf.OpenCohomology.inclusionRestrict {X : TopCat} {U V : TopologicalSpace.Opens ↑X} (i : V ⟶ U) : Functor (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat) (Sheaf ((Opens.grothendieckTopology ↑X).over V) AddCommGrpCat)
```

**Native source docstring:**

Restriction between over-sites induced by an inclusion of opens.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L417-L419) · native range starts at 417.

<a id="api-a650119ae4812dd1"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HPrimeIsoHOver`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.HPrimeIsoHOver {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] (n : ℕ) : (cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) n).comp ((evaluation (TopologicalSpace.Opens ↑X)ᵒᵖ AddCommGrpCat).obj (Opposite.op U)) ≅ (restrictToOver U).comp (functorH ((Opens.grothendieckTopology ↑X).over U) n)
```

**Native source docstring:**

`HPrimeEquivHOver` as a natural isomorphism in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L377-L389) · native range starts at 377.

<a id="api-cbf70235cc6700e4"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver_naturality`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] {G G' : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (f : G ⟶ G') (n : ℕ) (x : ↑(G.H' n U)) : (H.map ((restrictToOver U).map f) n) ((HPrimeEquivHOver U G n) x) = (HPrimeEquivHOver U G' n) ((ConcreteCategory.hom (((cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) n).map f).app (Opposite.op U))) x)
```

**Native source docstring:**

Naturality of `HPrimeEquivHOver` in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L354-L375) · native range starts at 354.

<a id="api-96f140158db9bac8"></a>

### `CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.HPrimeEquivHOver {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : ↑(G.H' n U) ≃+ ((restrictToOver U).obj G).H n
```

**Native source docstring:**

The additive equivalence between Ext-based cohomology over `U` and the
cohomology of the restricted sheaf on the over-site at `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L341-L351) · native range starts at 341.

<a id="api-f2726d6314c1ad98"></a>

### `CategoryTheory.Sheaf.OpenCohomology.cohomologySourceExtIso`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.cohomologySourceExtIso {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : Abelian.Ext (cohomologySource U) G n ≃+ Abelian.Ext (overConstantSource U) G n
```

**Native source docstring:**

Ext transport along `cohomologySourceIsoOverConstantSource`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L332-L339) · native range starts at 332.

<a id="api-b2af500f3ab1add4"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overExtEquiv`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overExtEquiv {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] [HasExt (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [HasExt (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] (F : Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat) (G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (n : ℕ) : Abelian.Ext ((restrictToOver U).leftAdjoint.obj F) G n ≃+ Abelian.Ext F ((restrictToOver U).obj G) n
```

**Native source docstring:**

The Ext equivalence induced by the adjunction between extension from and
restriction to the over-site at `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L317-L330) · native range starts at 317.

<a id="api-2a66a5bc45bb823f"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOver_preservesFiniteColimits`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.restrictToOver_preservesFiniteColimits {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] : Limits.PreservesFiniteColimits (restrictToOver U)
```

**Native source docstring:**

Restriction to an open over-site preserves finite colimits.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L300-L307) · native range starts at 300.

<a id="api-a824b928c85a7be1"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOver_preservesEpimorphisms`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.restrictToOver_preservesEpimorphisms {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] : (restrictToOver U).PreservesEpimorphisms
```

**Native source docstring:**

Restriction to an open over-site preserves epimorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L295-L298) · native range starts at 295.

<a id="api-282d6a840e89c002"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOver_epi`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.restrictToOver_epi {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (forget AddCommGrpCat)] {F G : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : F ⟶ G) [Epi a] : Epi ((restrictToOver U).map a)
```

**Native source docstring:**

Restriction to an open over-site preserves epimorphisms.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L254-L293) · native range starts at 254.

<a id="api-8c723c4f64bd3b54"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOver_leftAdjoint_preservesFiniteLimits`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.restrictToOver_leftAdjoint_preservesFiniteLimits {X : TopCat} (U : TopologicalSpace.Opens ↑X) [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] : Limits.PreservesFiniteLimits (restrictToOver U).leftAdjoint
```

**Native source docstring:**

The left adjoint to restriction to an open over-site preserves finite
limits.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L233-L249) · native range starts at 233.

<a id="api-713ecec2365255de"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overForgetOpLan_preservesFiniteLimits`

```lean
instance CategoryTheory.Sheaf.OpenCohomology.overForgetOpLan_preservesFiniteLimits {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Limits.PreservesFiniteLimits (Over.forget U).op.lan
```

**Native source docstring:**

Pointwise left Kan extension along the open over-site forgetful functor
preserves finite limits of abelian-group-valued presheaves.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L178-L231) · native range starts at 178.

<a id="api-ecf08cf7552d8d25"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overLanIndexIsEmpty`

```lean
theorem CategoryTheory.Sheaf.OpenCohomology.overLanIndexIsEmpty {X : TopCat} (U : TopologicalSpace.Opens ↑X) (V : (TopologicalSpace.Opens ↑X)ᵒᵖ) (hVU : ¬Opposite.unop V ≤ U) : IsEmpty (CostructuredArrow (Over.forget U).op V)
```

**Native source docstring:**

The pointwise left-Kan-extension index is empty outside `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L172-L176) · native range starts at 172.

<a id="api-3ce3a6a2bfdb4a80"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overLanIndexTerminal`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overLanIndexTerminal {X : TopCat} (U : TopologicalSpace.Opens ↑X) (V : (TopologicalSpace.Opens ↑X)ᵒᵖ) (hVU : Opposite.unop V ≤ U) : Limits.IsTerminal (overLanIndexTerminalObj U V hVU)
```

**Native source docstring:**

Terminality of `overLanIndexTerminalObj`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L148-L162) · native range starts at 148.

<a id="api-75d6f9559569c1f1"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overLanIndexTerminalObj`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overLanIndexTerminalObj {X : TopCat} (U : TopologicalSpace.Opens ↑X) (V : (TopologicalSpace.Opens ↑X)ᵒᵖ) (hVU : Opposite.unop V ≤ U) : CostructuredArrow (Over.forget U).op V
```

**Native source docstring:**

The canonical terminal object in the pointwise left-Kan-extension index
when the evaluated open lies below `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L140-L146) · native range starts at 140.

<a id="api-725616db7d359b3b"></a>

### `CategoryTheory.Sheaf.OpenCohomology.cohomologySourceIsoOverConstantSource`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.cohomologySourceIsoOverConstantSource {X : TopCat} (U : TopologicalSpace.Opens ↑X) : cohomologySource U ≅ overConstantSource U
```

**Native source docstring:**

The canonical isomorphism between the free-Yoneda cohomology source and
the left-adjoint image of the constant sheaf on the over-site at `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L133-L138) · native range starts at 133.

<a id="api-0b52de823dcbbc34"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overConstantSourceCorepresentableForSections`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overConstantSourceCorepresentableForSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) : (sectionsAtType U).CorepresentableBy (overConstantSource U)
```

**Native source docstring:**

The extended constant integral sheaf, viewed as a corepresenter of sections
over `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L127-L131) · native range starts at 127.

<a id="api-0c8119e12c582d74"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overSectionsAtTypeIso`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overSectionsAtTypeIso {X : TopCat} (U : TopologicalSpace.Opens ↑X) : overSectionsAtType U ≅ sectionsAtType U
```

**Native source docstring:**

Terminal-object sections on the over-site agree naturally with sections
over the corresponding open of `X`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L121-L125) · native range starts at 121.

<a id="api-2751fd3dbae8ada4"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overConstantSourceCorepresentable`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.overConstantSourceCorepresentable {X : TopCat} (U : TopologicalSpace.Opens ↑X) : (overSectionsAtType U).CorepresentableBy (overConstantSource U)
```

**Native source docstring:**

The extended constant integral sheaf corepresents terminal-object sections
on the over-site.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L106-L119) · native range starts at 106.

<a id="api-7f967194ff977f07"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overSectionsAtType`

```lean
abbrev CategoryTheory.Sheaf.OpenCohomology.overSectionsAtType {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Functor (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (Type u)
```

**Native source docstring:**

Sections over the terminal object of the over-site after restricting from
`X`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L96-L104) · native range starts at 96.

<a id="api-aee216b8efdc1c5d"></a>

### `CategoryTheory.Sheaf.OpenCohomology.overConstantSource`

```lean
noncomputable abbrev CategoryTheory.Sheaf.OpenCohomology.overConstantSource {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat
```

**Native source docstring:**

The extension to `X` of the constant integral sheaf on the over-site at
`U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L88-L94) · native range starts at 88.

<a id="api-d16be5a2060361b0"></a>

### `CategoryTheory.Sheaf.OpenCohomology.cohomologySourceCorepresentable`

```lean
noncomputable def CategoryTheory.Sheaf.OpenCohomology.cohomologySourceCorepresentable {X : TopCat} (U : TopologicalSpace.Opens ↑X) : (sectionsAtType U).CorepresentableBy (cohomologySource U)
```

**Native source docstring:**

The free-Yoneda source corepresents sections of abelian sheaves over `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L74-L86) · native range starts at 74.

<a id="api-1733e72bb9f62483"></a>

### `CategoryTheory.Sheaf.OpenCohomology.cohomologySource`

```lean
noncomputable abbrev CategoryTheory.Sheaf.OpenCohomology.cohomologySource {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat
```

**Native source docstring:**

The sheafified free-Yoneda object representing sections over `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L68-L72) · native range starts at 68.

<a id="api-cd0c08dfef3c5cef"></a>

### `CategoryTheory.Sheaf.OpenCohomology.sectionsAtType`

```lean
abbrev CategoryTheory.Sheaf.OpenCohomology.sectionsAtType {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Functor (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (Type u)
```

**Native source docstring:**

The functor of sections of a sheaf on `X` over `U`, valued in types.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L60-L66) · native range starts at 60.

<a id="api-689f64f4eede20ab"></a>

### `CategoryTheory.Sheaf.OpenCohomology.restrictToOver`

```lean
abbrev CategoryTheory.Sheaf.OpenCohomology.restrictToOver {X : TopCat} (U : TopologicalSpace.Opens ↑X) : Functor (Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)
```

**Native source docstring:**

Restriction of sheaves on `X` to the over-site at the open `U`.

[Frozen source](../SheafCohomology/OpenCohomology.lean#L56-L58) · native range starts at 56.

## `SheafCohomology.OpenCohomologyPushforwardResolution`

Scope: subject module.

<a id="api-f6d9b3f4ce2ee240"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : CategoryTheory.Functor (TopologicalSpace.Opens ↑Y)ᵒᵖ AddCommGrpCat} (h : pushforwardResolutionHomologyPresheaf f H q ⟶ Z) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.whiskerLeft ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a)) (CategoryTheory.CategoryStruct.comp (HPrimePushforwardResolutionHomologyPresheafIso f H q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimePushforwardResolutionHomologyPresheafIso f G q hq).hom (CategoryTheory.CategoryStruct.comp (pushforwardResolutionHomologyPresheafMap f a q) h)
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution presheaf
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1261-L1261) · native range starts at 1261.

<a id="api-b859bd662292934e"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp ((TopologicalSpace.Opens.map f).op.whiskerLeft ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a)) (HPrimePushforwardResolutionHomologyPresheafIso f H q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimePushforwardResolutionHomologyPresheafIso f G q hq).hom (pushforwardResolutionHomologyPresheafMap f a q)
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution presheaf
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1259-L1273) · native range starts at 1259.

<a id="api-fbc0cbcb4a2ac90e"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : (pushforwardResolutionHomologyPresheaf f H q).obj (Opposite.op V) ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op ((TopologicalSpace.Opens.map f).obj V))) (CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj H f V q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f V q hq).hom (CategoryTheory.CategoryStruct.comp ((pushforwardResolutionHomologyPresheafMap f a q).app (Opposite.op V)) h)
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution comparison is
natural in the coefficient sheaf at each target open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1241-L1241) · native range starts at 1241.

<a id="api-14df3813d9f37528"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op ((TopologicalSpace.Opens.map f).obj V))) (HPrimeIsoPushforwardResolutionHomologyPresheafObj H f V q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f V q hq).hom ((pushforwardResolutionHomologyPresheafMap f a q).app (Opposite.op V))
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution comparison is
natural in the coefficient sheaf at each target open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1239-L1257) · native range starts at 1239.

<a id="api-6351caaa2f0a45f8"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (pushforwardResolutionSections f V H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsMap ((TopologicalSpace.Opens.map f).obj V) a) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections H f V) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f V) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsCoefficientMap f V a) q) h)
```

**Native source docstring:**

The global-sections/pushforward comparison intertwines coefficient maps
on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1221-L1221) · native range starts at 1221.

<a id="api-52b9ff83f8ff9a4c"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsMap ((TopologicalSpace.Opens.map f).obj V) a) q) (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections H f V) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f V) q).hom (HomologicalComplex.homologyMap (pushforwardResolutionSectionsCoefficientMap f V a) q)
```

**Native source docstring:**

The global-sections/pushforward comparison intertwines coefficient maps
on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1219-L1237) · native range starts at 1219.

<a id="api-14bd985665593450"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) {Z : CochainComplex AddCommGrpCat ℕ} (h : pushforwardResolutionSections f V H ⟶ Z) : CategoryTheory.CategoryStruct.comp (globalResolutionSectionsMap ((TopologicalSpace.Opens.map f).obj V) a) (CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections H f V).hom h) = CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections G f V).hom (CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsCoefficientMap f V a) h)
```

**Native source docstring:**

The definitional global-sections/pushforward comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1204-L1204) · native range starts at 1204.

<a id="api-fc1721ee01a06648"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) : CategoryTheory.CategoryStruct.comp (globalResolutionSectionsMap ((TopologicalSpace.Opens.map f).obj V) a) (globalResolutionSectionsIsoPushforwardResolutionSections H f V).hom = CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections G f V).hom (pushforwardResolutionSectionsCoefficientMap f V a)
```

**Native source docstring:**

The definitional global-sections/pushforward comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1202-L1215) · native range starts at 1202.

<a id="api-052cbf18f4ec194b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) {Z : AddCommGrpCat} (h : (pushforwardResolutionHomologyPresheaf f H q).obj (Opposite.op V) ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsCoefficientMap f V a) q) (CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso H f V q).hom h) = CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso G f V q).hom (CategoryTheory.CategoryStruct.comp ((pushforwardResolutionHomologyPresheafMap f a q).app (Opposite.op V)) h)
```

**Native source docstring:**

Evaluation commutes naturally with the coefficient map on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1167-L1167) · native range starts at 1167.

<a id="api-bf44a716353009d8"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsCoefficientMap f V a) q) (pushforwardResolutionSectionsHomologyIso H f V q).hom = CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso G f V q).hom ((pushforwardResolutionHomologyPresheafMap f a q).app (Opposite.op V))
```

**Native source docstring:**

Evaluation commutes naturally with the coefficient map on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1166-L1198) · native range starts at 1166.

<a id="api-5f63f025e7dc920b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionHomologyPresheafMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionHomologyPresheafMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) : pushforwardResolutionHomologyPresheaf f G q ⟶ pushforwardResolutionHomologyPresheaf f H q
```

**Native source docstring:**

The coefficient map on pointwise homology of the pushed-forward fixed
injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1155-L1162) · native range starts at 1155.

<a id="api-c5e22be8e798d528"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsCoefficientMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsCoefficientMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (V : TopologicalSpace.Opens ↑Y) (a : G ⟶ H) : pushforwardResolutionSections f V G ⟶ pushforwardResolutionSections f V H
```

**Native source docstring:**

Evaluating the pushed-forward canonical descent at an open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1146-L1153) · native range starts at 1146.

<a id="api-123bb9bae50c5307"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionPresheafComplexMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionPresheafComplexMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : pushforwardResolutionPresheafComplex f G ⟶ pushforwardResolutionPresheafComplex f H
```

**Native source docstring:**

Pushing forward the canonical descent between fixed injective resolutions.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1138-L1144) · native range starts at 1138.

<a id="api-52395e922eabc289"></a>

### `TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero_suffix`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero_suffix (Y : TopCat) (V : TopologicalSpace.Opens ↑Y) : ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑Y)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).PreservesZeroMorphisms
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1125-L1128) · native range starts at 1125.

<a id="api-83b850416a889157"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive_suffix`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive_suffix (Y : TopCat) : (forget AddCommGrpCat Y).Additive
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1121-L1123) · native range starts at 1121.

<a id="api-8c9132773bd756b0"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality_assoc {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionSections U H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op U)) (CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology U H q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology U G q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsMap U a) q) h)
```

**Native source docstring:**

The positive local-cohomology/fixed-global-resolution-sections comparison
is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1100-L1100) · native range starts at 1100.

<a id="api-332cb53e3d5916c7"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op U)) (HPrimeIsoGlobalResolutionSectionsHomology U H q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology U G q hq).hom (HomologicalComplex.homologyMap (globalResolutionSectionsMap U a) q)
```

**Native source docstring:**

The positive local-cohomology/fixed-global-resolution-sections comparison
is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1098-L1113) · native range starts at 1098.

<a id="api-fadab0bdcc8f2e31"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality_assoc {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionHomComplex U H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op U)) (CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology U H q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology U G q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexMap U a) q) h)
```

**Native source docstring:**

The positive Ext/fixed-global-resolution comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1080-L1080) · native range starts at 1080.

<a id="api-61f15a62d6d1ca4a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op U)) (HPrimeIsoGlobalResolutionHomComplexHomology U H q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology U G q hq).hom (HomologicalComplex.homologyMap (globalResolutionHomComplexMap U a) q)
```

**Native source docstring:**

The positive Ext/fixed-global-resolution comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1078-L1096) · native range starts at 1078.

<a id="api-adf0719de38d3f2b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality_assoc {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionSections U H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexMap U a) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections U H) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections U G) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsMap U a) q) h)
```

**Native source docstring:**

Naturality on homology of the additive-Hom/sections comparison.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1062-L1062) · native range starts at 1062.

<a id="api-33394dc7e17f07fc"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexMap U a) q) (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections U H) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections U G) q).hom (HomologicalComplex.homologyMap (globalResolutionSectionsMap U a) q)
```

**Native source docstring:**

Naturality on homology of the additive-Hom/sections comparison.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1061-L1076) · native range starts at 1061.

<a id="api-9b803388b0e85eaa"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_coefficient_naturality_assoc {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) {Z : CochainComplex AddCommGrpCat ℕ} (h : globalResolutionSections U H ⟶ Z) : CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexMap U a) (CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections U H).hom h) = CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections U G).hom (CategoryTheory.CategoryStruct.comp (globalResolutionSectionsMap U a) h)
```

**Native source docstring:**

The additive-Hom/sections complex comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1049-L1049) · native range starts at 1049.

<a id="api-cc48d1864a47280b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_coefficient_naturality {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexMap U a) (globalResolutionHomComplexIsoSections U H).hom = CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections U G).hom (globalResolutionSectionsMap U a)
```

**Native source docstring:**

The additive-Hom/sections complex comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1047-L1059) · native range starts at 1047.

<a id="api-89be64a31950df36"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsMap {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : globalResolutionSections U G ⟶ globalResolutionSections U H
```

**Native source docstring:**

The map on fixed-global-resolution section complexes induced by a
coefficient morphism.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1040-L1045) · native range starts at 1040.

<a id="api-746bea5649021c43"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexMap {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : globalResolutionHomComplex U G ⟶ globalResolutionHomComplex U H
```

**Native source docstring:**

The map of additive-coyoneda complexes induced by canonical global
injective-resolution descent.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1029-L1038) · native range starts at 1029.

<a id="api-3aa4faaf846b007a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalAcyclicResolutionHom`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalAcyclicResolutionHom {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution (CategoryTheory.Sheaf.OpenCohomology.cohomologySource U) (CategoryTheory.injectiveResolution G)).Hom (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution (CategoryTheory.Sheaf.OpenCohomology.cohomologySource U) (CategoryTheory.injectiveResolution H)) a
```

**Native source docstring:**

The canonical global descent as a morphism of `Ext`-acyclic
resolutions.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1015-L1027) · native range starts at 1015.

<a id="api-28460c96e5136ab0"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalInjectiveResolutionHom`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalInjectiveResolutionHom {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : (CategoryTheory.injectiveResolution G).cocomplex ⟶ (CategoryTheory.injectiveResolution H).cocomplex
```

**Native source docstring:**

The canonical descent between the fixed global injective resolutions of a
coefficient morphism.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L1007-L1013) · native range starts at 1007.

<a id="api-34d31435cb0c0081"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimePushforwardResolutionHomologyPresheafIso {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {Y : TopCat} (f : X ⟶ Y) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : (TopologicalSpace.Opens.map f).op.comp ((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G) ≅ pushforwardResolutionHomologyPresheaf f G q
```

**Native source docstring:**

Positive local cohomology over inverse images, as a presheaf on the
target, is pointwise homology of the pushed-forward fixed canonical injective
resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L970-L986) · native range starts at 970.

<a id="api-5eecfe15ed914602"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : (pushforwardResolutionHomologyPresheaf f G q).obj (Opposite.op W) ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map ((TopologicalSpace.Opens.map f).map i).op) (CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f W q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f V q hq).hom (CategoryTheory.CategoryStruct.comp ((pushforwardResolutionHomologyPresheaf f G q).map i.op) h)
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution comparison is
natural under restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L942-L942) · native range starts at 942.

<a id="api-0dc54e3c03f03d9d"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map ((TopologicalSpace.Opens.map f).map i).op) (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f W q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoPushforwardResolutionHomologyPresheafObj G f V q hq).hom ((pushforwardResolutionHomologyPresheaf f G q).map i.op)
```

**Native source docstring:**

The positive local-cohomology/pushed-forward-resolution comparison is
natural under restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L940-L958) · native range starts at 940.

<a id="api-0c1b5715f97e7259"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoPushforwardResolutionHomologyPresheafObj {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) (q : ℕ) (hq : 0 < q) : G.H' q ((TopologicalSpace.Opens.map f).obj V) ≅ (pushforwardResolutionHomologyPresheaf f G q).obj (Opposite.op V)
```

**Native source docstring:**

Positive local cohomology over `f ⁻¹ V` is the value at `V` of the
pointwise homology presheaf of the pushed-forward fixed global injective
resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L910-L922) · native range starts at 910.

<a id="api-ad5f7aaf5a432eba"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (pushforwardResolutionSections f W G) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap ((TopologicalSpace.Opens.map f).map i) G) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f W) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f V) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsMap G f V i) q) h)
```

**Native source docstring:**

The definitional global-sections/pushforward identification intertwines
the corresponding maps on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L891-L891) · native range starts at 891.

<a id="api-d154daa7a708832c"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap ((TopologicalSpace.Opens.map f).map i) G) q) (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f W) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionSectionsIsoPushforwardResolutionSections G f V) q).hom (HomologicalComplex.homologyMap (pushforwardResolutionSectionsMap G f V i) q)
```

**Native source docstring:**

The definitional global-sections/pushforward identification intertwines
the corresponding maps on homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L889-L908) · native range starts at 889.

<a id="api-ccd812063c8110e8"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) {Z : CochainComplex AddCommGrpCat ℕ} (h : pushforwardResolutionSections f W G ⟶ Z) : CategoryTheory.CategoryStruct.comp (globalResolutionSectionsOpenMap ((TopologicalSpace.Opens.map f).map i) G) (CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections G f W).hom h) = CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections G f V).hom (CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsMap G f V i) h)
```

**Native source docstring:**

The componentwise global-sections/pushforward identification is natural
under restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L854-L854) · native range starts at 854.

<a id="api-3667a76013c257a0"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) : CategoryTheory.CategoryStruct.comp (globalResolutionSectionsOpenMap ((TopologicalSpace.Opens.map f).map i) G) (globalResolutionSectionsIsoPushforwardResolutionSections G f W).hom = CategoryTheory.CategoryStruct.comp (globalResolutionSectionsIsoPushforwardResolutionSections G f V).hom (pushforwardResolutionSectionsMap G f V i)
```

**Native source docstring:**

The componentwise global-sections/pushforward identification is natural
under restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L852-L869) · native range starts at 852.

<a id="api-893630d4c600d36e"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsOpenMap_eq_pushforwardResolutionSectionsMap`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsOpenMap_eq_pushforwardResolutionSectionsMap {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) : globalResolutionSectionsOpenMap ((TopologicalSpace.Opens.map f).map i) G = pushforwardResolutionSectionsMap G f V i
```

**Native source docstring:**

Under the definitional global-sections/pushforward identification,
restriction over a mapped open is the evaluated pushforward restriction.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L826-L832) · native range starts at 826.

<a id="api-cb42624f758ee7ea"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsIsoPushforwardResolutionSections {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : globalResolutionSections ((TopologicalSpace.Opens.map f).obj V) G ≅ pushforwardResolutionSections f V G
```

**Native source docstring:**

Sections of the fixed global injective resolution over `f ⁻¹ V` are
definitionally the evaluation at `V` of its pushed-forward complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L800-L807) · native range starts at 800.

<a id="api-1db630d48988493b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology_hom_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op ((TopologicalSpace.Opens.map f).obj V))) (CategoryTheory.CategoryStruct.comp (HPrimeIsoRestrictedResolutionSectionsHomology H f V q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoRestrictedResolutionSectionsHomology G f V q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (restrictedResolutionSectionsMap G f V a) q) h)
```

**Native source docstring:**

The positive-degree local-cohomology/terminal-sections comparison is
natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L764-L764) · native range starts at 764.

<a id="api-3a00c655039414b3"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology_hom_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology_hom_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).map a).app (Opposite.op ((TopologicalSpace.Opens.map f).obj V))) (HPrimeIsoRestrictedResolutionSectionsHomology H f V q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoRestrictedResolutionSectionsHomology G f V q hq).hom (HomologicalComplex.homologyMap (restrictedResolutionSectionsMap G f V a) q)
```

**Native source docstring:**

The positive-degree local-cohomology/terminal-sections comparison is
natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L762-L792) · native range starts at 762.

<a id="api-e991b71ab2199c02"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoRestrictedResolutionSectionsHomology {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : G.H' q ((TopologicalSpace.Opens.map f).obj V) ≅ HomologicalComplex.homology (restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) G) q
```

**Native source docstring:**

The positive-degree local-cohomology comparison as an isomorphism in
`AddCommGrpCat`.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L747-L758) · native range starts at 747.

<a id="api-b545438ae74951a9"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H).homComplex q ⟶ Z) : CategoryTheory.CategoryStruct.comp ((CategoryTheory.Sheaf.functorH ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) q).map ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver ((TopologicalSpace.Opens.map f).obj V)).map a)) (CategoryTheory.CategoryStruct.comp (restrictedAcyclicResolutionExtPositiveIso H f V q hq).hom h) = CategoryTheory.CategoryStruct.comp (restrictedAcyclicResolutionExtPositiveIso G f V q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) q) h)
```

**Native source docstring:**

Naturality of the positive-degree acyclic-resolution comparison for the
restricted canonical descents.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L727-L727) · native range starts at 727.

<a id="api-cb4a05a01ed3ac50"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp ((CategoryTheory.Sheaf.functorH ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) q).map ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver ((TopologicalSpace.Opens.map f).obj V)).map a)) (restrictedAcyclicResolutionExtPositiveIso H f V q hq).hom = CategoryTheory.CategoryStruct.comp (restrictedAcyclicResolutionExtPositiveIso G f V q hq).hom (HomologicalComplex.homologyMap ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) q)
```

**Native source docstring:**

Naturality of the positive-degree acyclic-resolution comparison for the
restricted canonical descents.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L725-L745) · native range starts at 725.

<a id="api-ce6dc86fceef65d8"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolutionExtPositiveIso`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolutionExtPositiveIso {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : (CategoryTheory.Sheaf.functorH ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) q).obj ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver ((TopologicalSpace.Opens.map f).obj V)).obj G) ≅ HomologicalComplex.homology (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplex q
```

**Native source docstring:**

The positive-degree acyclic-resolution comparison bundled in
`AddCommGrpCat`.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L697-L719) · native range starts at 697.

<a id="api-98e47caaef27f8ae"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) H) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) H) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) G) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (restrictedResolutionSectionsMap G f V a) q) h)
```

**Native source docstring:**

Naturality on homology of the additive-Hom/terminal-sections comparison.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L677-L677) · native range starts at 677.

<a id="api-9a91c62a86e51799"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) q) (HomologicalComplex.homologyMapIso (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) H) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) G) q).hom (HomologicalComplex.homologyMap (restrictedResolutionSectionsMap G f V a) q)
```

**Native source docstring:**

Naturality on homology of the additive-Hom/terminal-sections comparison.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L676-L695) · native range starts at 676.

<a id="api-7221f196053e6568"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections_hom_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) {Z : CochainComplex AddCommGrpCat ℕ} (h : restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) H ⟶ Z) : CategoryTheory.CategoryStruct.comp ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) (CategoryTheory.CategoryStruct.comp (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) H).hom h) = CategoryTheory.CategoryStruct.comp (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) G).hom (CategoryTheory.CategoryStruct.comp (restrictedResolutionSectionsMap G f V a) h)
```

**Native source docstring:**

The additive-Hom/terminal-sections complex comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L656-L656) · native range starts at 656.

<a id="api-8b5ca7b681d88349"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections_hom_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections_hom_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : CategoryTheory.CategoryStruct.comp ((restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).homComplexMap (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) (restrictedAcyclicResolutionHom G f V a).hom) (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) H).hom = CategoryTheory.CategoryStruct.comp (restrictedResolutionHomComplexIsoSections ((TopologicalSpace.Opens.map f).obj V) G).hom (restrictedResolutionSectionsMap G f V a)
```

**Native source docstring:**

The additive-Hom/terminal-sections complex comparison is natural in the
coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L654-L670) · native range starts at 654.

<a id="api-32c852aa61f2fe95"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSectionsMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSectionsMap {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) G ⟶ restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) H
```

**Native source docstring:**

The map on terminal-section complexes induced by a coefficient morphism.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L642-L648) · native range starts at 642.

<a id="api-ad120dea2596d206"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolutionHom`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolutionHom {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) G).Hom (restrictedAcyclicResolution ((TopologicalSpace.Opens.map f).obj V) H) ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver ((TopologicalSpace.Opens.map f).obj V)).map a)
```

**Native source docstring:**

The restricted canonical descent as a morphism of acyclic resolutions.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L616-L640) · native range starts at 616.

<a id="api-32840f210f5c20cb"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedInjectiveResolutionHom`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedInjectiveResolutionHom {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] {H : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G ⟶ H) : (restrictedInjectiveResolution ((TopologicalSpace.Opens.map f).obj V) G).cocomplex ⟶ (restrictedInjectiveResolution ((TopologicalSpace.Opens.map f).obj V) H).cocomplex
```

**Native source docstring:**

The canonical descent of a coefficient morphism, restricted to the open
over-site.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L606-L614) · native range starts at 606.

<a id="api-a40a4294b2e3e4f7"></a>

### `TopCat.Sheaf.RightDerivedPushforward.localCohomologyEquivPushforwardResolutionHomologyPresheafObj`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.localCohomologyEquivPushforwardResolutionHomologyPresheafObj {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : ↑(G.H' q ((TopologicalSpace.Opens.map f).obj V)) ≃+ ↑((pushforwardResolutionHomologyPresheaf f G q).obj (Opposite.op V))
```

**Native source docstring:**

Positive local cohomology over `f ⁻¹ V` is the value at `V` of the
pointwise homology presheaf of the pushed-forward canonical injective
resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L589-L599) · native range starts at 589.

<a id="api-4295fb6ff4b6cf33"></a>

### `TopCat.Sheaf.RightDerivedPushforward.localCohomologyEquivPushforwardResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.localCohomologyEquivPushforwardResolutionSectionsHomology {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : ↑(G.H' q ((TopologicalSpace.Opens.map f).obj V)) ≃+ ↑(HomologicalComplex.homology (pushforwardResolutionSections f V G) q)
```

**Native source docstring:**

Positive local cohomology over `f ⁻¹ V` is the homology at `V` of the
pushed-forward canonical injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L577-L587) · native range starts at 577.

<a id="api-9e1693b583cf3967"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) {Z : AddCommGrpCat} (h : (pushforwardResolutionHomologyPresheaf f G q).obj (Opposite.op W) ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsMap G f V i) q) (CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso G f W q).hom h) = CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso G f V q).hom (CategoryTheory.CategoryStruct.comp ((pushforwardResolutionHomologyPresheaf f G q).map i.op) h)
```

**Native source docstring:**

Pointwise homology of the pushed-forward resolution is natural under
restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L543-L543) · native range starts at 543.

<a id="api-2d397051d6df267c"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso_hom_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSectionsMap G f V i) q) (pushforwardResolutionSectionsHomologyIso G f W q).hom = CategoryTheory.CategoryStruct.comp (pushforwardResolutionSectionsHomologyIso G f V q).hom ((pushforwardResolutionHomologyPresheaf f G q).map i.op)
```

**Native source docstring:**

Pointwise homology of the pushed-forward resolution is natural under
restriction of the ambient open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L541-L573) · native range starts at 541.

<a id="api-ef675ca3a14653d1"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsMap {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) {W : TopologicalSpace.Opens ↑Y} (i : W ⟶ V) : pushforwardResolutionSections f V G ⟶ pushforwardResolutionSections f W G
```

**Native source docstring:**

Restriction on the evaluated pushed-forward injective-resolution
complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L512-L521) · native range starts at 512.

<a id="api-d2b690d06b61d245"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSectionsHomologyIso {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) (q : ℕ) : HomologicalComplex.homology (pushforwardResolutionSections f V G) q ≅ (pushforwardResolutionHomologyPresheaf f G q).obj (Opposite.op V)
```

**Native source docstring:**

Homology after evaluation agrees with evaluation of pointwise presheaf
homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L493-L506) · native range starts at 493.

<a id="api-636c59f3b24755aa"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSectionsIsoPushforwardResolutionSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSectionsIsoPushforwardResolutionSections {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)) AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over ((TopologicalSpace.Opens.map f).obj V)).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] : restrictedResolutionSections ((TopologicalSpace.Opens.map f).obj V) G ≅ pushforwardResolutionSections f V G
```

**Native source docstring:**

The terminal-sections complex after restriction to `f ⁻¹ V` is
canonically isomorphic to evaluation at `V` of the pushed-forward complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L480-L491) · native range starts at 480.

<a id="api-128267c88c5c6b6d"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedSectionsIsoPushforwardSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedSectionsIsoPushforwardSections {X Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (CategoryTheory.Sheaf.OpenCohomology.restrictToOver ((TopologicalSpace.Opens.map f).obj V)).comp (overTerminalSectionsFunctor ((TopologicalSpace.Opens.map f).obj V)) ≅ ((pushforward AddCommGrpCat f).comp (forget AddCommGrpCat Y)).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑Y)ᵒᵖ AddCommGrpCat).obj (Opposite.op V))
```

**Native source docstring:**

Restriction to `f ⁻¹ V` followed by terminal evaluation agrees with
evaluation at `V` after pushforward.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L470-L478) · native range starts at 470.

<a id="api-496ebea83009e79a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionHomologyPresheaf`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionHomologyPresheaf {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {Y : TopCat} (f : X ⟶ Y) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) : Presheaf AddCommGrpCat Y
```

**Native source docstring:**

Pointwise homology of the underlying pushed-forward canonical
injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L447-L454) · native range starts at 447.

<a id="api-def423aed86caa34"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSections`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSections {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

Evaluation at an open of the underlying pushed-forward canonical
injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L436-L445) · native range starts at 436.

<a id="api-6d8895f489066c1a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionPresheafComplex`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionPresheafComplex {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {Y : TopCat} (f : X ⟶ Y) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex (Presheaf AddCommGrpCat Y) ℕ
```

**Native source docstring:**

The underlying presheaf complex of the pushed-forward canonical
injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L425-L434) · native range starts at 425.

<a id="api-475924471c3cf140"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeEquivRestrictedResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeEquivRestrictedResolutionSectionsHomology {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : ↑(G.H' q U) ≃+ ↑(HomologicalComplex.homology (restrictedResolutionSections U G) q)
```

**Native source docstring:**

Positive local cohomology is the homology of terminal sections of the
restricted canonical injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L414-L423) · native range starts at 414.

<a id="api-117f605c642a256e"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionHomComplexIsoSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : (restrictedAcyclicResolution U G).homComplex ≅ restrictedResolutionSections U G
```

**Native source docstring:**

The additive-Hom complex in the acyclic-resolution comparison is the
terminal-sections complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L406-L412) · native range starts at 406.

<a id="api-868c403b66173995"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSections`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.restrictedResolutionSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

Terminal sections of the restricted injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L400-L404) · native range starts at 400.

<a id="api-e61b6f3bf9072d70"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.restrictedAcyclicResolution {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CategoryTheory.Abelian.Ext.AcyclicResolution ((CategoryTheory.constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj ↧(ULift.{u, 0} ℤ)) ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U).obj G)
```

**Native source docstring:**

The restricted injective resolution, viewed as an acyclic resolution for
the constant integral source.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L390-L398) · native range starts at 390.

<a id="api-85d7e6d2d0587d01"></a>

### `TopCat.Sheaf.RightDerivedPushforward.restrictedInjectiveResolution`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.restrictedInjectiveResolution {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [(Opens.grothendieckTopology ↑X).WEqualsLocallyBijective AddCommGrpCat] [(Opens.grothendieckTopology ↑X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] [((Opens.grothendieckTopology ↑X).over U).HasSheafCompose (CategoryTheory.forget AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CategoryTheory.InjectiveResolution ((CategoryTheory.Sheaf.OpenCohomology.restrictToOver U).obj G)
```

**Native source docstring:**

Restrict the canonical injective resolution to the open over-site.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L385-L388) · native range starts at 385.

<a id="api-e5b9653f644d8dc1"></a>

### `TopCat.Sheaf.RightDerivedPushforward.instAdditiveSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.instAdditiveSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] : (CategoryTheory.Sheaf.OpenCohomology.restrictToOver U).Additive
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L379-L380) · native range starts at 379.

<a id="api-d19941df2fde0e38"></a>

### `TopCat.Sheaf.RightDerivedPushforward.instPreservesInjectiveObjectsSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.instPreservesInjectiveObjectsSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] : (CategoryTheory.Sheaf.OpenCohomology.restrictToOver U).PreservesInjectiveObjects
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L374-L377) · native range starts at 374.

<a id="api-20240a15080838e9"></a>

### `TopCat.Sheaf.RightDerivedPushforward.overCoyonedaIsoSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.overCoyonedaIsoSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] : CategoryTheory.preadditiveCoyoneda.obj (Opposite.op ((CategoryTheory.constantSheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat).obj ↧(ULift.{u, 0} ℤ))) ≅ overTerminalSectionsFunctor U
```

**Native source docstring:**

Additive coyoneda from the constant integral sheaf is terminal evaluation
on the open over-site.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L361-L372) · native range starts at 361.

<a id="api-31fe17dce75f2f16"></a>

### `TopCat.Sheaf.RightDerivedPushforward.overFunctorHZeroIsoSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.overFunctorHZeroIsoSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat)] : CategoryTheory.Sheaf.functorH ((Opens.grothendieckTopology ↑X).over U) 0 ≅ overTerminalSectionsFunctor U
```

**Native source docstring:**

Degree-zero cohomology on the open over-site is terminal evaluation.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L347-L359) · native range starts at 347.

<a id="api-157cbadc13bc1e62"></a>

### `TopCat.Sheaf.RightDerivedPushforward.overTerminalSectionsFunctor`

```lean
abbrev TopCat.Sheaf.RightDerivedPushforward.overTerminalSectionsFunctor {X : TopCat} (U : TopologicalSpace.Opens ↑X) : CategoryTheory.Functor (CategoryTheory.Sheaf ((Opens.grothendieckTopology ↑X).over U) AddCommGrpCat) AddCommGrpCat
```

**Native source docstring:**

Evaluation at the terminal object of the open over-site.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L338-L345) · native range starts at 338.

<a id="api-a859bffd9030dfba"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionSections W G) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map i.op) (CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology W G q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology V G q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap i G) q) h)
```

**Native source docstring:**

The positive local-cohomology/fixed-resolution-sections comparison is
natural under restriction of the open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L320-L320) · native range starts at 320.

<a id="api-28b84925f5bddb4e"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map i.op) (HPrimeIsoGlobalResolutionSectionsHomology W G q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionSectionsHomology V G q hq).hom (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap i G) q)
```

**Native source docstring:**

The positive local-cohomology/fixed-resolution-sections comparison is
natural under restriction of the open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L318-L334) · native range starts at 318.

<a id="api-12cba0afc3c16bfa"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionSections W G) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexOpenMap i G) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections W G) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections V G) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap i G) q) h)
```

**Native source docstring:**

The Hom-complex/sections comparison intertwines the corresponding maps on
homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L297-L297) · native range starts at 297.

<a id="api-3933cb7552492b7b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexOpenMap i G) q) (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections W G) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (globalResolutionHomComplexIsoSections V G) q).hom (HomologicalComplex.homologyMap (globalResolutionSectionsOpenMap i G) q)
```

**Native source docstring:**

The Hom-complex/sections comparison intertwines the corresponding maps on
homology.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L295-L312) · native range starts at 295.

<a id="api-8a93d6562ccf9acb"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) {Z : CochainComplex AddCommGrpCat ℕ} (h : globalResolutionSections W G ⟶ Z) : CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexOpenMap i G) (CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections W G).hom h) = CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections V G).hom (CategoryTheory.CategoryStruct.comp (globalResolutionSectionsOpenMap i G) h)
```

**Native source docstring:**

The Hom-complex/sections comparison intertwines source precomposition and
restriction of sections.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L277-L277) · native range starts at 277.

<a id="api-cce74c748b45fa0b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexOpenMap i G) (globalResolutionHomComplexIsoSections W G).hom = CategoryTheory.CategoryStruct.comp (globalResolutionHomComplexIsoSections V G).hom (globalResolutionSectionsOpenMap i G)
```

**Native source docstring:**

The Hom-complex/sections comparison intertwines source precomposition and
restriction of sections.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L275-L289) · native range starts at 275.

<a id="api-50f1e5da21edafe7"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality_assoc {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) {Z : AddCommGrpCat} (h : HomologicalComplex.homology (globalResolutionHomComplex W G) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map i.op) (CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology W G q hq).hom h) = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology V G q hq).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (globalResolutionHomComplexOpenMap i G) q) h)
```

**Native source docstring:**

The positive Ext/fixed-resolution comparison is natural under restriction
of the open, viewed as precomposition by the free-Yoneda source map.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L257-L257) · native range starts at 257.

<a id="api-c19ebe076ca96aad"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↑X) q).obj G).map i.op) (HPrimeIsoGlobalResolutionHomComplexHomology W G q hq).hom = CategoryTheory.CategoryStruct.comp (HPrimeIsoGlobalResolutionHomComplexHomology V G q hq).hom (HomologicalComplex.homologyMap (globalResolutionHomComplexOpenMap i G) q)
```

**Native source docstring:**

The positive Ext/fixed-resolution comparison is natural under restriction
of the open, viewed as precomposition by the free-Yoneda source map.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L255-L269) · native range starts at 255.

<a id="api-fa7098fa2b7355ad"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsOpenMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionSectionsOpenMap {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : globalResolutionSections V G ⟶ globalResolutionSections W G
```

**Native source docstring:**

Restriction of sections on the fixed injective-resolution complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L241-L249) · native range starts at 241.

<a id="api-ee92c21f1457a044"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexOpenMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexOpenMap {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : globalResolutionHomComplex V G ⟶ globalResolutionHomComplex W G
```

**Native source docstring:**

Precomposition by the source map on the fixed resolution Hom complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L232-L239) · native range starts at 232.

<a id="api-2e8d74e3798bec18"></a>

### `TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections_hom_open_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections_hom_open_naturality_assoc {X : TopCat} {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) {Z : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) AddCommGrpCat} (h : openSectionsFunctor W ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.preadditiveCoyoneda.map ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).map (((CategoryTheory.Functor.whiskeringRight (TopologicalSpace.Opens ↑X)ᵒᵖ (Type u) AddCommGrpCat).obj AddCommGrpCat.free).map (CategoryTheory.yoneda.map i))).op) (CategoryTheory.CategoryStruct.comp (cohomologySourceCoyonedaIsoSections W).hom h) = CategoryTheory.CategoryStruct.comp (cohomologySourceCoyonedaIsoSections V).hom (CategoryTheory.CategoryStruct.comp ((CategoryTheory.sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat).map i.op) h)
```

**Native source docstring:**

The free-Yoneda additive-coyoneda/sections comparison is natural under
restriction of the open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L191-L191) · native range starts at 191.

<a id="api-0c0cb837bf239f76"></a>

### `TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections_hom_open_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections_hom_open_naturality {X : TopCat} {V W : TopologicalSpace.Opens ↑X} (i : W ⟶ V) : CategoryTheory.CategoryStruct.comp (CategoryTheory.preadditiveCoyoneda.map (CategoryTheory.Sheaf.OpenCohomology.globalCohomologySourceFunctor.map i).op) (cohomologySourceCoyonedaIsoSections W).hom = CategoryTheory.CategoryStruct.comp (cohomologySourceCoyonedaIsoSections V).hom ((CategoryTheory.sheafSections (Opens.grothendieckTopology ↑X) AddCommGrpCat).map i.op)
```

**Native source docstring:**

The free-Yoneda additive-coyoneda/sections comparison is natural under
restriction of the open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L189-L230) · native range starts at 189.

<a id="api-8e3d84296e37461f"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeEquivGlobalResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeEquivGlobalResolutionSectionsHomology {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : ↑(G.H' q U) ≃+ ↑(HomologicalComplex.homology (globalResolutionSections U G) q)
```

**Native source docstring:**

Positive local cohomology as the homology of sections of the fixed
canonical injective resolution, as an additive equivalence.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L168-L176) · native range starts at 168.

<a id="api-e4f5f9b3d1b11353"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionSectionsHomology {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : G.H' q U ≅ HomologicalComplex.homology (globalResolutionSections U G) q
```

**Native source docstring:**

Positive local cohomology as the homology of sections of the fixed
canonical injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L157-L166) · native range starts at 157.

<a id="api-062bd0c0113e3538"></a>

### `TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.HPrimeIsoGlobalResolutionHomComplexHomology {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : G.H' q U ≅ HomologicalComplex.homology (globalResolutionHomComplex U G) q
```

**Native source docstring:**

Positive local cohomology as the homology of the additive-coyoneda complex
of the fixed canonical injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L131-L155) · native range starts at 131.

<a id="api-36665e85a662d75a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplexIsoSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : globalResolutionHomComplex U G ≅ globalResolutionSections U G
```

**Native source docstring:**

The additive-coyoneda resolution complex is the complex of sections over
the corresponding open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L122-L129) · native range starts at 122.

<a id="api-7fd537a331a70fab"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionSections`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.globalResolutionSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

Sections over an open of the fixed canonical injective-resolution
complex.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L114-L120) · native range starts at 114.

<a id="api-12cf5087e8fbc434"></a>

### `TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplex`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.globalResolutionHomComplex {X : TopCat} (U : TopologicalSpace.Opens ↑X) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex AddCommGrpCat ℕ
```

**Native source docstring:**

The additive-coyoneda complex from the cohomology source into the fixed
canonical injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L106-L112) · native range starts at 106.

<a id="api-8962beab1ee025d2"></a>

### `TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.cohomologySourceCoyonedaIsoSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) : CategoryTheory.preadditiveCoyoneda.obj (Opposite.op (CategoryTheory.Sheaf.OpenCohomology.cohomologySource U)) ≅ openSectionsFunctor U
```

**Native source docstring:**

Additive coyoneda from the free-Yoneda cohomology source is sections over
the corresponding open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L94-L104) · native range starts at 94.

<a id="api-617c8ab1fd669949"></a>

### `TopCat.Sheaf.RightDerivedPushforward.cohomologySourceHomAddEquivSections`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.cohomologySourceHomAddEquivSections {X : TopCat} (U : TopologicalSpace.Opens ↑X) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : (CategoryTheory.Sheaf.OpenCohomology.cohomologySource U ⟶ F) ≃+ ↑((openSectionsFunctor U).obj F)
```

**Native source docstring:**

The additive form of the free-Yoneda corepresentation of sections over
an open.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L82-L92) · native range starts at 82.

<a id="api-cce65c0afeb9d187"></a>

### `TopCat.Sheaf.RightDerivedPushforward.openSectionsFunctor`

```lean
abbrev TopCat.Sheaf.RightDerivedPushforward.openSectionsFunctor {X : TopCat} (U : TopologicalSpace.Opens ↑X) : CategoryTheory.Functor (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) AddCommGrpCat
```

**Native source docstring:**

Sections over an open, valued in additive commutative groups.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L75-L80) · native range starts at 75.

<a id="api-73b11716a33065f0"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardSections_preservesZero`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardSections_preservesZero {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {Y : TopCat} (f : X ⟶ Y) (V : TopologicalSpace.Opens ↑Y) : (((pushforward AddCommGrpCat f).comp (forget AddCommGrpCat Y)).comp ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑Y)ᵒᵖ AddCommGrpCat).obj (Opposite.op V))).PreservesZeroMorphisms
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L68-L73) · native range starts at 68.

<a id="api-66b70f81fbe1dcf6"></a>

### `TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero (Y : TopCat) (V : TopologicalSpace.Opens ↑Y) : ((CategoryTheory.evaluation (TopologicalSpace.Opens ↑Y)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).PreservesZeroMorphisms
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L63-L66) · native range starts at 63.

<a id="api-ee40ef18dd5258eb"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive (Y : TopCat) : (forget AddCommGrpCat Y).Additive
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L59-L61) · native range starts at 59.

<a id="api-53d41fb404aa9ef6"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforward_additive`

```lean
instance TopCat.Sheaf.RightDerivedPushforward.pushforward_additive {X : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {Y : TopCat} (f : X ⟶ Y) : (pushforward AddCommGrpCat f).Additive
```

**Native source docstring:**

Pushforward of additive-commutative-group-valued sheaves is additive.

[Frozen source](../SheafCohomology/OpenCohomologyPushforwardResolution.lean#L53-L57) · native range starts at 53.

## `SheafCohomology.OpenCohomologyRightDerived`

Scope: subject module.

<a id="api-7cde3b70a85e12dd"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (hq : 0 < q) : sheafifiedLocalCohomologyFunctor f q ≅ (pushforward AddCommGrpCat f).rightDerived q
```

**Native source docstring:**

In positive degree, sheafified local cohomology along a continuous map is
the corresponding right-derived pushforward, naturally in the coefficient
sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L518-L531) · native range starts at 518.

<a id="api-af3e994129282651"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) {Z : Sheaf AddCommGrpCat Y} (h : ((pushforward AddCommGrpCat f).rightDerived q).obj G₂ ⟶ Z) : CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) (CategoryTheory.CategoryStruct.comp (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom h) = CategoryTheory.CategoryStruct.comp (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom (CategoryTheory.CategoryStruct.comp (((pushforward AddCommGrpCat f).rightDerived q).map a) h)
```

**Native source docstring:**

The positive sheafified-local-cohomology/right-derived-pushforward
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L457-L457) · native range starts at 457.

<a id="api-a626f73e5cad8404"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom = CategoryTheory.CategoryStruct.comp (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom (((pushforward AddCommGrpCat f).rightDerived q).map a)
```

**Native source docstring:**

The positive sheafified-local-cohomology/right-derived-pushforward
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L455-L514) · native range starts at 455.

<a id="api-7d1e6735b6c349a1"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) {Z : Sheaf AddCommGrpCat Y} (h : HomologicalComplex.homology (pushforwardResolutionSheafComplex f G₂) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology f G₂ q hq).hom) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology f G₁ q hq).hom (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q)) h
```

**Native source docstring:**

The sheafified-local-cohomology/pushed-forward-resolution-homology
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L324-L324) · native range starts at 324.

<a id="api-44c4c7a5ecc7a27d"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology f G₂ q hq).hom = CategoryTheory.CategoryStruct.comp (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology f G₁ q hq).hom (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q)
```

**Native source docstring:**

The sheafified-local-cohomology/pushed-forward-resolution-homology
comparison is natural in the coefficient sheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L322-L453) · native range starts at 322.

<a id="api-cca31d0c097b9cc3"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj_inv_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj_inv_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) {Z : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat} (h : ((pushforward AddCommGrpCat f).rightDerived q).obj G₂ ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q) (pushforwardIsoRightDerivedObj f G₂ q).inv) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (pushforwardIsoRightDerivedObj f G₁ q).inv (((pushforward AddCommGrpCat f).rightDerived q).map a)) h
```

**Native source docstring:**

The inverse right-derived-functor comparison is natural in the
coefficient sheaf for canonical injective-resolution descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L296-L296) · native range starts at 296.

<a id="api-aaecf6f460b1a7a3"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj_inv_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj_inv_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q) (pushforwardIsoRightDerivedObj f G₂ q).inv = CategoryTheory.CategoryStruct.comp (pushforwardIsoRightDerivedObj f G₁ q).inv (((pushforward AddCommGrpCat f).rightDerived q).map a)
```

**Native source docstring:**

The inverse right-derived-functor comparison is natural in the
coefficient sheaf for canonical injective-resolution descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L294-L320) · native range starts at 294.

<a id="api-1bf4ab5dc5c0a10f"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) {Z : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat} (h : HomologicalComplex.homology (pushforwardResolutionSheafComplex f G₂) q ⟶ Z) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (sheafifiedPushforwardResolutionComplexMap f a) q) (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom h) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q) h)
```

**Native source docstring:**

The sheafified-complex/pushed-forward-sheaf-complex comparison
intertwines coefficient maps on homology.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L276-L276) · native range starts at 276.

<a id="api-9cc73cc4a8effa92"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (sheafifiedPushforwardResolutionComplexMap f a) q) (HomologicalComplex.homologyMapIso (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMapIso (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom (HomologicalComplex.homologyMap (pushforwardResolutionSheafComplexMap f a) q)
```

**Native source docstring:**

The sheafified-complex/pushed-forward-sheaf-complex comparison
intertwines coefficient maps on homology.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L274-L290) · native range starts at 274.

<a id="api-393e52f62aab74ff"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) {Z : HomologicalComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat) (ComplexShape.up ℕ)} (h : pushforwardResolutionSheafComplex f G₂ ⟶ Z) : CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionComplexMap f a) (CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionComplexIso f G₂).hom h) = CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionComplexIso f G₁).hom (CategoryTheory.CategoryStruct.comp (pushforwardResolutionSheafComplexMap f a) h)
```

**Native source docstring:**

The complex comparison from sheafified underlying pushforward to sheaf
pushforward is natural in the coefficient descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L258-L258) · native range starts at 258.

<a id="api-878fadd209412715"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) : CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionComplexMap f a) (sheafifiedPushforwardResolutionComplexIso f G₂).hom = CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionComplexIso f G₁).hom (pushforwardResolutionSheafComplexMap f a)
```

**Native source docstring:**

The complex comparison from sheafified underlying pushforward to sheaf
pushforward is natural in the coefficient descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L256-L270) · native range starts at 256.

<a id="api-d67099d27c584d11"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) {Z : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat} (h : (((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (pushforwardResolutionPresheafComplex f G₂)).homology q ⟶ Z) : CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionHomologyMap f a q) (CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv h) = CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv (CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (sheafifiedPushforwardResolutionComplexMap f a) q) h)
```

**Native source docstring:**

Sheafification's homology comparison is natural in the coefficient
descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L223-L223) · native range starts at 223.

<a id="api-d70bc9f0592d77ad"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) : CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionHomologyMap f a q) (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv = CategoryTheory.CategoryStruct.comp (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv (HomologicalComplex.homologyMap (sheafifiedPushforwardResolutionComplexMap f a) q)
```

**Native source docstring:**

Sheafification's homology comparison is natural in the coefficient
descent.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L221-L252) · native range starts at 221.

<a id="api-15bc3f34c198b2b9"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality_assoc`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality_assoc {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) {Z : Sheaf AddCommGrpCat Y} (h : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).obj (pushforwardResolutionHomologyPresheaf f G₂ q) ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapIso (HPrimePushforwardResolutionHomologyPresheafIso f G₂ q hq)).hom) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapIso (HPrimePushforwardResolutionHomologyPresheafIso f G₁ q hq)).hom (sheafifiedPushforwardResolutionHomologyMap f a q)) h
```

**Native source docstring:**

Mapping the positive presheaf comparison through sheafification preserves
its coefficient-naturality square.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L186-L186) · native range starts at 186.

<a id="api-0331885f7f86371a"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) : CategoryTheory.CategoryStruct.comp ((sheafifiedLocalCohomologyFunctor f q).map a) ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapIso (HPrimePushforwardResolutionHomologyPresheafIso f G₂ q hq)).hom = CategoryTheory.CategoryStruct.comp ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapIso (HPrimePushforwardResolutionHomologyPresheafIso f G₁ q hq)).hom (sheafifiedPushforwardResolutionHomologyMap f a q)
```

**Native source docstring:**

Mapping the positive presheaf comparison through sheafification preserves
its coefficient-naturality square.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L184-L217) · native range starts at 184.

<a id="api-769287e127eaa116"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSheafComplexMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSheafComplexMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) : pushforwardResolutionSheafComplex f G₁ ⟶ pushforwardResolutionSheafComplex f G₂
```

**Native source docstring:**

The coefficient map on the pushed-forward fixed injective-resolution
complex in sheaves.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L176-L182) · native range starts at 176.

<a id="api-a3eeb095f83b9344"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) : ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (pushforwardResolutionPresheafComplex f G₁) ⟶ ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (pushforwardResolutionPresheafComplex f G₂)
```

**Native source docstring:**

Sheafification of the coefficient map on the pushed-forward presheaf
resolution complexes.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L158-L174) · native range starts at 158.

<a id="api-6d02b349029c50cf"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionHomologyMap`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionHomologyMap {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] {G₁ G₂ : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat} (a : G₁ ⟶ G₂) (q : ℕ) : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).obj (pushforwardResolutionHomologyPresheaf f G₁ q) ⟶ (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).obj (pushforwardResolutionHomologyPresheaf f G₂ q)
```

**Native source docstring:**

Sheafification of the coefficient map on the pointwise homology
presheaf.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L144-L156) · native range starts at 144.

<a id="api-192ae0959ed45978"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoRightDerivedObj {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : sheafifiedLocalCohomology f G q ≅ ((pushforward AddCommGrpCat f).rightDerived q).obj G
```

**Native source docstring:**

Positive sheafified local cohomology agrees objectwise with the right
derived pushforward.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L129-L137) · native range starts at 129.

<a id="api-f7e6b9d42d849dc0"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.pushforwardIsoRightDerivedObj {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) : ((pushforward AddCommGrpCat f).rightDerived q).obj G ≅ HomologicalComplex.homology (pushforwardResolutionSheafComplex f G) q
```

**Native source docstring:**

The canonical right-derived-functor comparison with the pushed-forward
fixed injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L119-L127) · native range starts at 119.

<a id="api-ce7c7c16c5670f58"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyIsoPushforwardResolutionHomology {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] [CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) (hq : 0 < q) : sheafifiedLocalCohomology f G q ≅ HomologicalComplex.homology (pushforwardResolutionSheafComplex f G) q
```

**Native source docstring:**

The sheafification of positive local cohomology is homology of the
pushed-forward fixed canonical injective resolution.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L99-L117) · native range starts at 99.

<a id="api-e9d9a1ec7c1adacf"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionHomologyIso`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionHomologyIso {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) (q : ℕ) : (((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (pushforwardResolutionPresheafComplex f G)).homology q ≅ (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).obj (pushforwardResolutionHomologyPresheaf f G q)
```

**Native source docstring:**

Sheafification's canonical comparison between homology after mapping the
resolution complex and sheafification of its pointwise homology.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L81-L97) · native range starts at 81.

<a id="api-938356e31e729cc7"></a>

### `TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso`

```lean
noncomputable def TopCat.Sheaf.RightDerivedPushforward.sheafifiedPushforwardResolutionComplexIso {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj (pushforwardResolutionPresheafComplex f G) ≅ pushforwardResolutionSheafComplex f G
```

**Native source docstring:**

Sheafifying the underlying pushed-forward resolution complex recovers the
pushed-forward sheaf complex.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L62-L79) · native range starts at 62.

<a id="api-f1ddbe4888368e4b"></a>

### `TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSheafComplex`

```lean
noncomputable abbrev TopCat.Sheaf.RightDerivedPushforward.pushforwardResolutionSheafComplex {X Y : TopCat} (f : X ⟶ Y) [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] (G : CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat) : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat) ℕ
```

**Native source docstring:**

The fixed canonical injective resolution after sheaf pushforward.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L55-L60) · native range starts at 55.

<a id="api-caa1cf523d642434"></a>

### `TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesHomology_sheafification`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesHomology_sheafification {Y : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).PreservesHomology
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L39-L43) · native range starts at 39.

<a id="api-92f379327f843436"></a>

### `TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesZero_sheafification`

```lean
theorem TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesZero_sheafification {Y : TopCat} [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑Y) AddCommGrpCat] : (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑Y) AddCommGrpCat).PreservesZeroMorphisms
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/OpenCohomologyRightDerived.lean#L31-L37) · native range starts at 31.

## `SheafCohomology.PullbackCoherence`

Scope: subject module.

<a id="api-239faecfa512de0d"></a>

### `TopCat.Sheaf.pullbackCompIso_assoc`

```lean
theorem TopCat.Sheaf.pullbackCompIso_assoc (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z W : TopCat} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (pullback A h).isoWhiskerLeft (pullbackCompIso A f g) ≪≫ pullbackCompIso A (CategoryTheory.CategoryStruct.comp f g) h = ((pullback A h).associator (pullback A g) (pullback A f)).symm ≪≫ CategoryTheory.Functor.isoWhiskerRight (pullbackCompIso A g h) (pullback A f) ≪≫ pullbackCompIso A f (CategoryTheory.CategoryStruct.comp g h)
```

**Native source docstring:**

The two canonical comparisons from a triple iterated pullback to pullback
along the triple composite agree.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L204-L216) · native range starts at 204.

<a id="api-16e17fd9055eed06"></a>

### `TopCat.Sheaf.pullbackCompIso_id_comp`

```lean
theorem TopCat.Sheaf.pullbackCompIso_id_comp (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y : TopCat} (f : X ⟶ Y) : pullbackCompIso A f (CategoryTheory.CategoryStruct.id Y) = CategoryTheory.Functor.isoWhiskerRight (pullbackIdIso A Y) (pullback A f) ≪≫ (pullback A f).leftUnitor
```

**Native source docstring:**

Pullback composition agrees with the identity comparison when the second
map is an identity.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L179-L186) · native range starts at 179.

<a id="api-8869cab06b2d8afb"></a>

### `TopCat.Sheaf.pullbackCompIso_comp_id`

```lean
theorem TopCat.Sheaf.pullbackCompIso_comp_id (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y : TopCat} (f : X ⟶ Y) : pullbackCompIso A (CategoryTheory.CategoryStruct.id X) f = (pullback A f).isoWhiskerLeft (pullbackIdIso A X) ≪≫ (pullback A f).rightUnitor
```

**Native source docstring:**

Pullback composition agrees with the identity comparison when the first
map is an identity.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L170-L177) · native range starts at 170.

<a id="api-6565ccb435b9bc62"></a>

### `TopCat.Sheaf.pullbackIdInv_naturality`

```lean
theorem TopCat.Sheaf.pullbackIdInv_naturality (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] (X : TopCat) {F G : Sheaf A X} (α : F ⟶ G) : CategoryTheory.CategoryStruct.comp α (pullbackIdInv A X G) = CategoryTheory.CategoryStruct.comp (pullbackIdInv A X F) ((pullback A (CategoryTheory.CategoryStruct.id X)).map α)
```

**Native source docstring:**

The inverse identity-pullback comparison is natural in the sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L137-L142) · native range starts at 137.

<a id="api-7e17fece5664048d"></a>

### `TopCat.Sheaf.pullbackIdHom_naturality`

```lean
theorem TopCat.Sheaf.pullbackIdHom_naturality (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] (X : TopCat) {F G : Sheaf A X} (α : F ⟶ G) : CategoryTheory.CategoryStruct.comp ((pullback A (CategoryTheory.CategoryStruct.id X)).map α) (pullbackIdHom A X G) = CategoryTheory.CategoryStruct.comp (pullbackIdHom A X F) α
```

**Native source docstring:**

The forward identity-pullback comparison is natural in the sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L130-L135) · native range starts at 130.

<a id="api-d4b3335c21cc4a66"></a>

### `TopCat.Sheaf.pullbackIdInv`

```lean
noncomputable abbrev TopCat.Sheaf.pullbackIdInv (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] (X : TopCat) (F : Sheaf A X) : F ⟶ (pullback A (CategoryTheory.CategoryStruct.id X)).obj F
```

**Native source docstring:**

The inverse identity-pullback comparison on one sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L125-L128) · native range starts at 125.

<a id="api-c5fb6393559bf996"></a>

### `TopCat.Sheaf.pullbackIdHom`

```lean
noncomputable abbrev TopCat.Sheaf.pullbackIdHom (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] (X : TopCat) (F : Sheaf A X) : (pullback A (CategoryTheory.CategoryStruct.id X)).obj F ⟶ F
```

**Native source docstring:**

The identity-pullback comparison on one sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L120-L123) · native range starts at 120.

<a id="api-a8658e2bb43e5497"></a>

### `TopCat.Sheaf.pullbackIdIso`

```lean
noncomputable def TopCat.Sheaf.pullbackIdIso (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] (X : TopCat) : pullback A (CategoryTheory.CategoryStruct.id X) ≅ CategoryTheory.Functor.id (Sheaf A X)
```

**Native source docstring:**

Pullback along the identity is canonically isomorphic to the identity functor.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L108-L112) · native range starts at 108.

<a id="api-642dca48f7eda70c"></a>

### `TopCat.Sheaf.pullbackCompInv_naturality`

```lean
theorem TopCat.Sheaf.pullbackCompInv_naturality (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) {F G : Sheaf A Z} (α : F ⟶ G) : CategoryTheory.CategoryStruct.comp ((pullback A (CategoryTheory.CategoryStruct.comp f g)).map α) (pullbackCompInv A f g G) = CategoryTheory.CategoryStruct.comp (pullbackCompInv A f g F) ((pullback A f).map ((pullback A g).map α))
```

**Native source docstring:**

The inverse composite-pullback comparison is natural in the sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L100-L106) · native range starts at 100.

<a id="api-44525b055c1f25b8"></a>

### `TopCat.Sheaf.pullbackCompHom_naturality`

```lean
theorem TopCat.Sheaf.pullbackCompHom_naturality (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) {F G : Sheaf A Z} (α : F ⟶ G) : CategoryTheory.CategoryStruct.comp ((pullback A f).map ((pullback A g).map α)) (pullbackCompHom A f g G) = CategoryTheory.CategoryStruct.comp (pullbackCompHom A f g F) ((pullback A (CategoryTheory.CategoryStruct.comp f g)).map α)
```

**Native source docstring:**

The forward composite-pullback comparison is natural in the sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L92-L98) · native range starts at 92.

<a id="api-85fb0457c03acbc1"></a>

### `TopCat.Sheaf.pullbackCompInv`

```lean
noncomputable abbrev TopCat.Sheaf.pullbackCompInv (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf A Z) : (pullback A (CategoryTheory.CategoryStruct.comp f g)).obj F ⟶ (pullback A f).obj ((pullback A g).obj F)
```

**Native source docstring:**

The inverse composite-pullback comparison on one sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L85-L90) · native range starts at 85.

<a id="api-dc3d751169d5c6b1"></a>

### `TopCat.Sheaf.pullbackCompHom`

```lean
noncomputable abbrev TopCat.Sheaf.pullbackCompHom (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (F : Sheaf A Z) : (pullback A f).obj ((pullback A g).obj F) ⟶ (pullback A (CategoryTheory.CategoryStruct.comp f g)).obj F
```

**Native source docstring:**

The forward composite-pullback comparison on one sheaf.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L78-L83) · native range starts at 78.

<a id="api-8d39cd77e6bb6877"></a>

### `TopCat.Sheaf.pullbackCompIso`

```lean
noncomputable def TopCat.Sheaf.pullbackCompIso (A : Type u) [CategoryTheory.Category.{w, u} A] {FA : A → A → Type u_1} {CA : A → Type w} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)] [CategoryTheory.ConcreteCategory A FA] [CategoryTheory.Limits.HasColimits A] [CategoryTheory.Limits.HasLimits A] [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget A)] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget A)] [(CategoryTheory.forget A).ReflectsIsomorphisms] {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (pullback A g).comp (pullback A f) ≅ pullback A (CategoryTheory.CategoryStruct.comp f g)
```

**Native source docstring:**

Pullback along a composite is canonically isomorphic to iterated pullback.

[Frozen source](../SheafCohomology/PullbackCoherence.lean#L59-L66) · native range starts at 59.

## `SheafCohomology.QuasiFlasque`

Scope: subject module.

<a id="api-b89b9af02c3ed30a"></a>

### `TopCat.Sheaf.IsQuasiFlasque.isQuasiFlasque_colimit`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.isQuasiFlasque_colimit {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] {FC : C → C → Type u_1} {CC : C → Type v} [(A B : C) → FunLike (FC A B) (CC A) (CC B)] [instCC : CategoryTheory.ConcreteCategory C FC] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] [CategoryTheory.Limits.HasLimitsOfSize.{u, u, v, v + 1} C] [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)] [CategoryTheory.Limits.PreservesLimitsOfSize.{u, u, v, v, v + 1, v + 1} (CategoryTheory.forget C)] [instReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms] [(Opens.grothendieckTopology X).WEqualsLocallyBijective C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] [∀ (i : I), IsQuasiFlasque (F.obj i)] : IsQuasiFlasque (CategoryTheory.Limits.colimit F)
```

**Native source docstring:**

On a compact prespectral, quasi-separated space, a filtered colimit of
quasi-flasque sheaves is quasi-flasque.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L117-L149) · native range starts at 117.

<a id="api-5917e511296f6972"></a>

### `TopCat.Sheaf.IsQuasiFlasque.colimit_map_restriction_comp_post_assoc`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.colimit_map_restriction_comp_post_assoc {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) {Z : C} (h : (SheafCohomology.CompactOpenSections.sectionsOf U).obj (CategoryTheory.Limits.colimit F) ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft (restriction U))) (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf U)) h) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf ⊤)) (CategoryTheory.CategoryStruct.comp ((restriction U).app (CategoryTheory.Limits.colimit F)) h)
```

**Native source docstring:**

The canonical colimit comparison is natural with respect to restriction
from the terminal open to `U`.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L104-L104) · native range starts at 104.

<a id="api-3eae93b3f2959694"></a>

### `TopCat.Sheaf.IsQuasiFlasque.colimit_map_restriction_comp_post`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.colimit_map_restriction_comp_post {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C] [CategoryTheory.Limits.HasColimitsOfSize.{v, v, v, v + 1} C] {I : Type v} [CategoryTheory.SmallCategory I] [CategoryTheory.IsFiltered I] (F : CategoryTheory.Functor I (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)) (U : TopologicalSpace.Opens X) : CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimMap (F.whiskerLeft (restriction U))) (CategoryTheory.Limits.colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf U)) = CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf ⊤)) ((restriction U).app (CategoryTheory.Limits.colimit F))
```

**Native source docstring:**

The canonical colimit comparison is natural with respect to restriction
from the terminal open to `U`.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L102-L113) · native range starts at 102.

<a id="api-2d36c8ce3bd84b62"></a>

### `TopCat.Sheaf.IsQuasiFlasque.iff_surjective`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.iff_surjective {X : Type u} [TopologicalSpace X] (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) : IsQuasiFlasque F ↔ ∀ (U : TopologicalSpace.Opens X), IsCompact ↑U → Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((restriction U).app F))
```

**Native source docstring:**

For a sheaf of types, quasi-flasqueness is exactly surjectivity of every
restriction from the terminal open to a compact open.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L66-L82) · native range starts at 66.

<a id="api-392cdb87fcfddfa7"></a>

### `TopCat.Sheaf.IsQuasiFlasque.of_isFlasque`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.of_isFlasque {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] (F : Sheaf C ↧X) [F.IsFlasque] : IsQuasiFlasque F
```

**Native source docstring:**

Every flasque sheaf is quasi-flasque.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L56-L63) · native range starts at 56.

<a id="api-845ad236eecb9312"></a>

### `TopCat.Sheaf.IsQuasiFlasque.epi_restriction`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.epi_restriction {X : Type u} {inst✝ : TopologicalSpace X} {C : Type (v + 1)} {inst✝¹ : CategoryTheory.Category.{v, v + 1} C} {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C} [self : IsQuasiFlasque F] (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.Epi ((restriction U).app F)
```

**No native source docstring.** See the source and module guide.

**Native nested structure_field display site** of [`TopCat.Sheaf.IsQuasiFlasque`](#api-9fac34dfdbb53ca2).

Native HTML text: `epi_restriction (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.Epi ((restriction U).app F)`

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L51-L51) · native range starts at 51.

<a id="api-c603754005b83143"></a>

### `TopCat.Sheaf.IsQuasiFlasque.mk`

```lean
constructor TopCat.Sheaf.IsQuasiFlasque.mk : ∀ {X : Type u} [inst : TopologicalSpace X] {C : Type (v + 1)} [inst_1 : CategoryTheory.Category.{v, v + 1} C] {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C}, (∀ (U : TopologicalSpace.Opens X), IsCompact ↑U → CategoryTheory.Epi ((TopCat.Sheaf.restriction U).app F)) → TopCat.Sheaf.IsQuasiFlasque F
```

**No native source docstring.** See the source and module guide.

**Native nested structure_fields display site** of [`TopCat.Sheaf.IsQuasiFlasque`](#api-9fac34dfdbb53ca2).

Native HTML text: `epi_restriction (U : TopologicalSpace.Opens X) (hU : IsCompact ↑U) : CategoryTheory.Epi ((restriction U).app F)`

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L46-L52) · native range starts at 46.

<a id="api-9fac34dfdbb53ca2"></a>

### `TopCat.Sheaf.IsQuasiFlasque`

```lean
class TopCat.Sheaf.IsQuasiFlasque {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) C) : Prop
```

**Native source docstring:**

A sheaf is quasi-flasque if global sections restrict
epimorphically to every compact open.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L46-L52) · native range starts at 46.

<a id="api-6cd52f0aed5662db"></a>

### `TopCat.Sheaf.restriction`

```lean
abbrev TopCat.Sheaf.restriction {X : Type u} [TopologicalSpace X] {C : Type (v + 1)} [CategoryTheory.Category.{v, v + 1} C] (U : TopologicalSpace.Opens X) : SheafCohomology.CompactOpenSections.sectionsOf ⊤ ⟶ SheafCohomology.CompactOpenSections.sectionsOf U
```

**Native source docstring:**

Restriction from global sections to sections on `U`.

[Frozen source](../SheafCohomology/QuasiFlasque.lean#L37-L44) · native range starts at 37.

## `SheafCohomology.QuasiFlasqueAcyclicity`

Scope: subject module.

<a id="api-7ecb57a8294b7c1d"></a>

### `TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.subsingleton_H_succ {X : TopCat} [CompactSpace ↑X] [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [CategoryTheory.HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat] [hExt : CategoryTheory.HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)] (q : ℕ) (G : Sheaf AddCommGrpCat X) [IsQuasiFlasque G] : Subsingleton (CategoryTheory.Sheaf.H G (q + 1))
```

**Native source docstring:**

A quasi-flasque abelian sheaf on a compact prespectral quasi-separated
space has trivial cohomology in every positive degree.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L257-L393) · native range starts at 257.

<a id="api-9faabbf0ca4bc7af"></a>

### `TopCat.Sheaf.IsQuasiFlasque.instCarrierAddCommGrpCatFlasqueInjectiveQuotientOfQuasiSeparatedSpaceOfPrespectralSpace`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.instCarrierAddCommGrpCatFlasqueInjectiveQuotientOfQuasiSeparatedSpaceOfPrespectralSpace {X : TopCat} (F : Sheaf AddCommGrpCat X) [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] [IsQuasiFlasque F] : IsQuasiFlasque (flasqueInjectiveQuotient F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L249-L254) · native range starts at 249.

<a id="api-88ce1770b836e8d4"></a>

### `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelopeShortExact`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelopeShortExact {X : TopCat} (F : Sheaf AddCommGrpCat X) : (flasqueInjectiveEnvelopeShortComplex F).ShortExact
```

**Native source docstring:**

The canonical kernel-envelope-quotient short complex is short exact.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L244-L247) · native range starts at 244.

<a id="api-6d93a73e81636991"></a>

### `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelopeShortComplex`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelopeShortComplex {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)
```

**Native source docstring:**

The canonical kernel-envelope-quotient short complex.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L237-L242) · native range starts at 237.

<a id="api-987a725b47458272"></a>

### `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveQuotient`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveQuotient {X : TopCat} (F : Sheaf AddCommGrpCat X) : Sheaf AddCommGrpCat X
```

**Native source docstring:**

The cokernel of the canonical map to the flasque injective envelope.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L233-L235) · native range starts at 233.

<a id="api-cf13eefb117c4921"></a>

### `TopCat.Sheaf.IsQuasiFlasque.instIsFlasqueAddCommGrpCatFlasqueInjectiveEnvelope`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.instIsFlasqueAddCommGrpCatFlasqueInjectiveEnvelope {X : TopCat} (F : Sheaf AddCommGrpCat X) : (flasqueInjectiveEnvelope F).IsFlasque
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L229-L231) · native range starts at 229.

<a id="api-7897dfb40a767aa6"></a>

### `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelope_injective`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelope_injective {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.Injective (flasqueInjectiveEnvelope F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L224-L227) · native range starts at 224.

<a id="api-c2a2b0f5ba08ad66"></a>

### `TopCat.Sheaf.IsQuasiFlasque.toFlasqueInjectiveEnvelope_mono`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.toFlasqueInjectiveEnvelope_mono {X : TopCat} (F : Sheaf AddCommGrpCat X) : CategoryTheory.Mono (toFlasqueInjectiveEnvelope F)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L193-L222) · native range starts at 193.

<a id="api-bfc414691300a6ea"></a>

### `TopCat.Sheaf.IsQuasiFlasque.toFlasqueInjectiveEnvelope`

```lean
noncomputable def TopCat.Sheaf.IsQuasiFlasque.toFlasqueInjectiveEnvelope {X : TopCat} (F : Sheaf AddCommGrpCat X) : F ⟶ flasqueInjectiveEnvelope F
```

**Native source docstring:**

The canonical map from `F` to its skyscraper-product injective envelope.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L188-L191) · native range starts at 188.

<a id="api-ea36b8101041e890"></a>

### `TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelope`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.flasqueInjectiveEnvelope {X : TopCat} (F : Sheaf AddCommGrpCat X) : Sheaf AddCommGrpCat X
```

**Native source docstring:**

The product, over all points, of the injective skyscraper envelopes of the stalks.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L184-L186) · native range starts at 184.

<a id="api-e6f9b5f818dfab7b"></a>

### `TopCat.Sheaf.IsQuasiFlasque.toStalkInjectiveSkyscraper_stalk_mono`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.toStalkInjectiveSkyscraper_stalk_mono {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : CategoryTheory.Mono ((Presheaf.stalkFunctor AddCommGrpCat x).map (toStalkInjectiveSkyscraper F x).hom)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L162-L182) · native range starts at 162.

<a id="api-2055c9e6ec0660d6"></a>

### `TopCat.Sheaf.IsQuasiFlasque.toStalkInjectiveSkyscraper`

```lean
noncomputable def TopCat.Sheaf.IsQuasiFlasque.toStalkInjectiveSkyscraper {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : F ⟶ stalkInjectiveSkyscraper F x
```

**Native source docstring:**

The adjunction unit followed by the chosen injective stalk embedding.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L156-L160) · native range starts at 156.

<a id="api-2c7f7d682c0731df"></a>

### `TopCat.Sheaf.IsQuasiFlasque.instIsFlasqueAddCommGrpCatStalkInjectiveSkyscraper`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.instIsFlasqueAddCommGrpCatStalkInjectiveSkyscraper {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : (stalkInjectiveSkyscraper F x).IsFlasque
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L151-L154) · native range starts at 151.

<a id="api-729c2da5b8cbc55b"></a>

### `TopCat.Sheaf.IsQuasiFlasque.instInjectiveAddCommGrpCatStalkInjectiveSkyscraper`

```lean
instance TopCat.Sheaf.IsQuasiFlasque.instInjectiveAddCommGrpCatStalkInjectiveSkyscraper {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : CategoryTheory.Injective (stalkInjectiveSkyscraper F x)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L148-L149) · native range starts at 148.

<a id="api-38e6b4f4298969ad"></a>

### `TopCat.Sheaf.IsQuasiFlasque.stalkInjectiveSkyscraper`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.stalkInjectiveSkyscraper {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : Sheaf AddCommGrpCat X
```

**Native source docstring:**

The skyscraper sheaf associated to the chosen injective envelope of `Fₓ`.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L144-L146) · native range starts at 144.

<a id="api-d74a414c8ccd1c72"></a>

### `TopCat.Sheaf.IsQuasiFlasque.stalkInjective`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.stalkInjective {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : AddCommGrpCat
```

**Native source docstring:**

A chosen injective object containing the stalk of `F` at `x`.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L140-L142) · native range starts at 140.

<a id="api-41e37b6a017a34f7"></a>

### `TopCat.Sheaf.IsQuasiFlasque.stalkObject`

```lean
noncomputable abbrev TopCat.Sheaf.IsQuasiFlasque.stalkObject {X : TopCat} (F : Sheaf AddCommGrpCat X) (x : ↑X) : AddCommGrpCat
```

**Native source docstring:**

The stalk of `F` at `x`, used in the skyscraper-product envelope.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L135-L138) · native range starts at 135.

<a id="api-d6e7d9353f800c71"></a>

### `TopCat.Sheaf.IsFlasque.product`

```lean
instance TopCat.Sheaf.IsFlasque.product {X : TopCat} {ι : Type u} (G : ι → Sheaf AddCommGrpCat X) [CategoryTheory.Limits.HasProduct G] [∀ (i : ι), (G i).IsFlasque] : (∏ᶜ G).IsFlasque
```

**Native source docstring:**

A product of flasque `AddCommGrpCat`-valued sheaves is flasque.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L71-L127) · native range starts at 71.

<a id="api-55d0e667423969c6"></a>

### `TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology`

```lean
noncomputable def TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology {X : TopCat} (x : ↑X) (U : TopologicalSpace.Opens ↑X) : Decidable (x ∈ U)
```

**Source-local instance registration.** This `local instance` is not a globally registered typeclass instance. This note does not assert explicit-name access.

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/QuasiFlasqueAcyclicity.lean#L50-L50) · native range starts at 50.

## `SheafCohomology.QuasiFlasqueExactness`

Scope: subject module.

<a id="api-713ba09eb235ad18"></a>

### `TopCat.Sheaf.IsQuasiFlasque.of_shortExact_of_isQuasiFlasque₁₂`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.of_shortExact_of_isQuasiFlasque₁₂ {X : TopCat} [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] {S : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) [IsQuasiFlasque S.X₁] [IsQuasiFlasque S.X₂] : IsQuasiFlasque S.X₃
```

**Native source docstring:**

In a prespectral quasi-separated space, a quotient of quasi-flasque
abelian sheaves in a short exact sequence is quasi-flasque.

[Frozen source](../SheafCohomology/QuasiFlasqueExactness.lean#L271-L289) · native range starts at 271.

<a id="api-930d206fd77ddf84"></a>

### `TopCat.Sheaf.IsQuasiFlasque.epi_of_shortExact`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.epi_of_shortExact {X : TopCat} [QuasiSeparatedSpace ↑X] [CompactSpace ↑X] [PrespectralSpace ↑X] {S : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) [IsQuasiFlasque S.X₁] : CategoryTheory.Epi (S.g.hom.app (Opposite.op ⊤))
```

**Native source docstring:**

On a compact prespectral quasi-separated space, a short exact sequence
whose kernel is quasi-flasque is surjective on global sections.

[Frozen source](../SheafCohomology/QuasiFlasqueExactness.lean#L263-L269) · native range starts at 263.

<a id="api-1ccd7fa48a235fa4"></a>

### `TopCat.Sheaf.IsQuasiFlasque.epi_app_of_shortExact`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.epi_app_of_shortExact {X : TopCat} [QuasiSeparatedSpace ↑X] [PrespectralSpace ↑X] {S : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) [IsQuasiFlasque S.X₁] (T : TopologicalSpace.Opens ↑X) (hTc : IsCompact ↑T) : CategoryTheory.Epi (S.g.hom.app (Opposite.op T))
```

**Native source docstring:**

In a prespectral quasi-separated space, a short exact sequence whose
kernel is quasi-flasque is surjective on every compact open.

[Frozen source](../SheafCohomology/QuasiFlasqueExactness.lean#L203-L261) · native range starts at 203.

<a id="api-468d701864e815a0"></a>

### `TopCat.Sheaf.IsQuasiFlasque.exists_lift_finset`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.exists_lift_finset {X : TopCat} [QuasiSeparatedSpace ↑X] {ι : Type u_1} [DecidableEq ι] {S : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) [IsQuasiFlasque S.X₁] (T : TopologicalSpace.Opens ↑X) (A : Finset ι) (U : ι → TopologicalSpace.Opens ↑X) (hUT : ∀ i ∈ A, U i ≤ T) (hUc : ∀ i ∈ A, IsCompact ↑(U i)) (s₃ : ↑(S.X₃.obj.obj (Opposite.op T))) (sU : (i : ι) → ↑(S.X₂.obj.obj (Opposite.op (U i)))) (hsU : ∀ (i : ι) (hi : i ∈ A), (CategoryTheory.ConcreteCategory.hom (S.g.hom.app (Opposite.op (U i)))) (sU i) = Presheaf.restrictOpen s₃ (U i) ⋯) : ∃ (s : ↑(S.X₂.obj.obj (Opposite.op (A.sup U)))), (CategoryTheory.ConcreteCategory.hom (S.g.hom.app (Opposite.op (A.sup U)))) s = Presheaf.restrictOpen s₃ (A.sup U) ⋯
```

**Native source docstring:**

A compatible family of local lifts on finitely many compact opens can be
corrected and glued to a lift on their union.

[Frozen source](../SheafCohomology/QuasiFlasqueExactness.lean#L145-L201) · native range starts at 145.

<a id="api-4a4f3dfcf95a8b20"></a>

### `TopCat.Sheaf.IsQuasiFlasque.exists_lift_sup`

```lean
theorem TopCat.Sheaf.IsQuasiFlasque.exists_lift_sup {X : TopCat} [QuasiSeparatedSpace ↑X] {S : CategoryTheory.ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) [IsQuasiFlasque S.X₁] (T U V : TopologicalSpace.Opens ↑X) (hUT : U ≤ T) (hVT : V ≤ T) (hUc : IsCompact ↑U) (hVc : IsCompact ↑V) (s₃ : ↑(S.X₃.obj.obj (Opposite.op T))) (sU : ↑(S.X₂.obj.obj (Opposite.op U))) (hsU : (CategoryTheory.ConcreteCategory.hom (S.g.hom.app (Opposite.op U))) sU = Presheaf.restrictOpen s₃ U hUT) (sV : ↑(S.X₂.obj.obj (Opposite.op V))) (hsV : (CategoryTheory.ConcreteCategory.hom (S.g.hom.app (Opposite.op V))) sV = Presheaf.restrictOpen s₃ V hVT) : ∃ (s : ↑(S.X₂.obj.obj (Opposite.op (U ⊔ V)))), (CategoryTheory.ConcreteCategory.hom (S.g.hom.app (Opposite.op (U ⊔ V)))) s = Presheaf.restrictOpen s₃ (U ⊔ V) ⋯
```

**Native source docstring:**

The two-open correction step in the quasi-flasque exactness argument.

[Frozen source](../SheafCohomology/QuasiFlasqueExactness.lean#L38-L132) · native range starts at 38.

## `SheafCohomology.SheafificationBasis`

Scope: subject module.

<a id="api-f190d91802095c1c"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.presheafToSheaf_map_isIso_of_isBasis`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.presheafToSheaf_map_isIso_of_isBasis {X : TopCat} {B : Set (TopologicalSpace.Opens ↑X)} (hB : TopologicalSpace.Opens.IsBasis B) {F G : TopCat.Presheaf AddCommGrpCat X} {α : F ⟶ G} (hα : ∀ U ∈ B, CategoryTheory.IsIso (α.app (Opposite.op U))) : CategoryTheory.IsIso ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).map α)
```

**Native source docstring:**

A morphism of `AddCommGrpCat`-valued presheaves that is an isomorphism on
a basis becomes an isomorphism after sheafification.

[Frozen source](../SheafCohomology/SheafificationBasis.lean#L53-L90) · native range starts at 53.

<a id="api-1022e7626c787d59"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.stalkFunctor_map_bijective_of_isBasis`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.stalkFunctor_map_bijective_of_isBasis {X : TopCat} {B : Set (TopologicalSpace.Opens ↑X)} (hB : TopologicalSpace.Opens.IsBasis B) {F G : TopCat.Presheaf AddCommGrpCat X} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Bijective ⇑(CategoryTheory.ConcreteCategory.hom (α.app (Opposite.op U)))) (x : ↑X) : Function.Bijective ⇑(CategoryTheory.ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map α))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SheafificationBasis.lean#L45-L51) · native range starts at 45.

<a id="api-2e9c1dd7f6e43ebf"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.stalkFunctor_map_surjective_of_isBasis`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.stalkFunctor_map_surjective_of_isBasis {X : TopCat} {B : Set (TopologicalSpace.Opens ↑X)} (hB : TopologicalSpace.Opens.IsBasis B) {F G : TopCat.Presheaf AddCommGrpCat X} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom (α.app (Opposite.op U)))) (x : ↑X) : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map α))
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SheafificationBasis.lean#L35-L43) · native range starts at 35.

## `SheafCohomology.SpectralPreimage`

Scope: subject module.

<a id="api-54b2b90c23dde68c"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimage_coherent_classes`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.preimage_coherent_classes {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace X] [QuasiSeparatedSpace X] {f : X → Y} (hf : IsSpectralMap f) (V : TopologicalSpace.Opens Y) (hV : IsCompact ↑V) : Nonempty (PrespectralSpace (preimageOpenType f V)) ∧ Nonempty (CompactSpace (preimageOpenType f V)) ∧ Nonempty (QuasiSeparatedSpace (preimageOpenType f V))
```

**Native source docstring:**

The prespectral, compact, and quasi-separated classes hold on a
compact-open preimage. The `Nonempty` wrappers keep this theorem independent of
global typeclass installation.

[Frozen source](../SheafCohomology/SpectralPreimage.lean#L48-L59) · native range starts at 48.

<a id="api-9e9f9e143e703f1d"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimageQuasiSeparatedSpace`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.preimageQuasiSeparatedSpace {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSeparatedSpace X] {f : X → Y} (hf : IsSpectralMap f) (V : TopologicalSpace.Opens Y) : QuasiSeparatedSpace (preimageOpenType f V)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SpectralPreimage.lean#L43-L46) · native range starts at 43.

<a id="api-4d3df3911351760c"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimageCompactSpace`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.preimageCompactSpace {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : IsSpectralMap f) (V : TopologicalSpace.Opens Y) (hV : IsCompact ↑V) : CompactSpace (preimageOpenType f V)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SpectralPreimage.lean#L38-L41) · native range starts at 38.

<a id="api-696f000c91537393"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimagePrespectralSpace`

```lean
theorem SheafCohomology.HigherDirectImageFilteredColimit.preimagePrespectralSpace {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace X] {f : X → Y} (hf : IsSpectralMap f) (V : TopologicalSpace.Opens Y) : PrespectralSpace (preimageOpenType f V)
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SpectralPreimage.lean#L33-L36) · native range starts at 33.

<a id="api-bddd3513076efc55"></a>

### `SheafCohomology.HigherDirectImageFilteredColimit.preimageOpenType`

```lean
abbrev SheafCohomology.HigherDirectImageFilteredColimit.preimageOpenType {X : Type uX} {Y : Type uY} [TopologicalSpace Y] (f : X → Y) (V : TopologicalSpace.Opens Y) : Type uX
```

**No native source docstring.** See the source and module guide.

[Frozen source](../SheafCohomology/SpectralPreimage.lean#L30-L31) · native range starts at 30.

## `SheafCohomology`

Scope: aggregate re-export.

No native public declaration display sites: this module provides public imports and module documentation only.

## `SheafCohomologyExamples`

Scope: private downstream examples.

No native public declaration display sites: this module provides private checked root-import examples.
