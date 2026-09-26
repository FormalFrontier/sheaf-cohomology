/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology

set_option warningAsError true

universe v

open CategoryTheory TopologicalSpace TopCat.Sheaf.AbelianForget

namespace SheafCohomologyExamples.AbelianForgetPullbackClient

variable {X Y Z : TopCat.{v}} (f : X ⟶ Y) (h : Y ⟶ Z)

/-- The public comparison is the actual Type-adjunction mate. -/
private theorem mate (A : Y.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv _ _
      (canonicalComponent f A) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).unit.app A) :=
  canonicalComponent_mate f A

/-- The arbitrary-morphism mate law is accessible through the public imports. -/
private theorem mate_map (A : Y.Sheaf AddCommGrpCat.{v}) (B : X.Sheaf AddCommGrpCat.{v})
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj A ⟶ B) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv _ _
      (canonicalComponent f A ≫ (underlyingSheaf X).map a) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv A B a) :=
  canonicalComponent_mate_map f A B a

/-- The canonical component has a natural inverse. -/
private theorem inverse (A : Y.Sheaf AddCommGrpCat.{v}) :
    (inverseComparisonIso f).inv.app A = canonicalComponent f A :=
  inverseComparisonIso_inv_app f A

/-- The comparison is invertible with no hypothesis on `f`. -/
private theorem invertible (A : Y.Sheaf AddCommGrpCat.{v}) :
    IsIso (canonicalComponent f A) := canonicalComponent_isIso f A

/-- Identity-pullback coherence is available for arbitrary spaces. -/
private theorem identity (A : X.Sheaf AddCommGrpCat.{v}) :
    canonicalComponent (𝟙 X) A ≫
        (underlyingSheaf X).map (TopCat.Sheaf.pullbackIdHom AddCommGrpCat.{v} X A) =
      TopCat.Sheaf.pullbackIdHom (Type v) X ((underlyingSheaf X).obj A) :=
  canonicalComponent_id X A

/-- Composition-pullback coherence is available for arbitrary maps. -/
private theorem composition (A : Z.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
        canonicalComponent f ((TopCat.Sheaf.pullback AddCommGrpCat.{v} h).obj A) ≫
          (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A) =
      TopCat.Sheaf.pullbackCompHom (Type v) f h ((underlyingSheaf Z).obj A) ≫
        canonicalComponent (f ≫ h) A :=
  canonicalComponent_comp f h A

/-- The identity comparison works on an empty space. -/
private theorem empty_space (A : (TopCat.of Empty).Sheaf AddCommGrpCat.{0}) :
    IsIso (canonicalComponent (𝟙 (TopCat.of Empty)) A) :=
  canonicalComponent_isIso (𝟙 (TopCat.of Empty)) A


end SheafCohomologyExamples.AbelianForgetPullbackClient
