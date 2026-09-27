module
import SheafCohomology.AbelianForget.SheafedSpace


set_option warningAsError true

/-!
# Public clients of additive-to-Type sheafed-space transport

All arrows below are native sheafed-space morphisms; the mate laws refer to
their actual presheaf structure maps, not freely chosen sheaf morphisms.
-/

universe v

open CategoryTheory TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.SheafedSpace.AbelianForget

namespace SheafCohomologyExamples.AbelianForgetSheafedSpaceClient

variable {X Y Z : SheafedSpace AddCommGrpCat.{v}}

/-- The exact structure-map direction is target to pushed-forward source. -/
private theorem arrow_structure (f : X ⟶ Y) :
    (underlying.map f).hom.c =
      CategoryTheory.Functor.whiskerRight f.hom.c
        (CategoryTheory.forget AddCommGrpCat.{v}) :=
  underlying_map_c f

/-- The ordinary native arrow satisfies the unassumed adjunction-mate law. -/
private theorem arrow_pullback_mate (f : X ⟶ Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f.hom.base).homEquiv
      ((TopCat.Sheaf.AbelianForget.underlyingSheaf (Y : TopCat)).obj Y.sheaf)
      ((TopCat.Sheaf.AbelianForget.underlyingSheaf (X : TopCat)).obj X.sheaf)).symm
        (⟨(underlying.map f).hom.c⟩) =
      TopCat.Sheaf.AbelianForget.canonicalComponent f.hom.base Y.sheaf ≫
        (TopCat.Sheaf.AbelianForget.underlyingSheaf (X : TopCat)).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f.hom.base).homEquiv
            Y.sheaf X.sheaf).symm (⟨f.hom.c⟩)) :=
  underlying_map_pullback_mate f

/-- Both actual arrows in a composable chain satisfy the mate law. -/
private theorem chain_mates (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f.hom.base).homEquiv _ _).symm
        (⟨(underlying.map f).hom.c⟩) =
      TopCat.Sheaf.AbelianForget.canonicalComponent f.hom.base Y.sheaf ≫
        (TopCat.Sheaf.AbelianForget.underlyingSheaf (X : TopCat)).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f.hom.base).homEquiv
            Y.sheaf X.sheaf).symm (⟨f.hom.c⟩)) ∧
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g.hom.base).homEquiv _ _).symm
        (⟨(underlying.map g).hom.c⟩) =
      TopCat.Sheaf.AbelianForget.canonicalComponent g.hom.base Z.sheaf ≫
        (TopCat.Sheaf.AbelianForget.underlyingSheaf (Y : TopCat)).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g.hom.base).homEquiv
            Z.sheaf Y.sheaf).symm (⟨g.hom.c⟩)) :=
  ⟨underlying_map_pullback_mate f, underlying_map_pullback_mate g⟩

/-- Forgetting preserves both native functor composition and its base map. -/
private theorem chain_composition (f : X ⟶ Y) (g : Y ⟶ Z) :
    underlying.map (f ≫ g) = underlying.map f ≫ underlying.map g ∧
      (underlying.map (f ≫ g)).hom.base = f.hom.base ≫ g.hom.base := by
  constructor
  · exact underlying.map_comp f g
  · simp

/-- The actual composite structure map is contravariant in the sheaves. -/
private theorem chain_structure (f : X ⟶ Y) (g : Y ⟶ Z) :
    (underlying.map (f ≫ g)).hom.c =
      CategoryTheory.Functor.whiskerRight
        (g.hom.c ≫ (TopCat.Presheaf.pushforward AddCommGrpCat.{v} g.hom.base).map f.hom.c)
        (CategoryTheory.forget AddCommGrpCat.{v}) :=
  underlying_map_c (f ≫ g)

/-- Identity maps retain their actual underlying maps and mate equation. -/
private theorem identity (X : SheafedSpace AddCommGrpCat.{v}) :
    underlying.map (𝟙 X) = 𝟙 (underlying.obj X) ∧
      ((underlying.map (𝟙 X)).hom.base = 𝟙 (X : TopCat)) := by
  constructor
  · exact underlying.map_id X
  · simp

/-- Empty-carrier additive sheafed spaces use exactly the supplied sheaf. -/
private def emptySheafed (A : (TopCat.of Empty).Sheaf AddCommGrpCat.{0}) :
    SheafedSpace AddCommGrpCat.{0} where
  carrier := TopCat.of Empty
  presheaf := A.1
  IsSheaf := A.2

private theorem empty_carrier (A : (TopCat.of Empty).Sheaf AddCommGrpCat.{0}) :
    ((underlying.obj (emptySheafed A) : SheafedSpace (Type 0)) : TopCat) =
      TopCat.of Empty := by
  simp [emptySheafed]

/-- The genuine mate law also holds for arrows between empty-carrier objects. -/
private theorem empty_arrow_mate (A B : (TopCat.of Empty).Sheaf AddCommGrpCat.{0})
    (f : emptySheafed A ⟶ emptySheafed B) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type 0) f.hom.base).homEquiv _ _).symm
        (⟨(underlying.map f).hom.c⟩) =
      TopCat.Sheaf.AbelianForget.canonicalComponent f.hom.base (emptySheafed B).sheaf ≫
        (TopCat.Sheaf.AbelianForget.underlyingSheaf (TopCat.of Empty)).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f.hom.base).homEquiv
            (emptySheafed B).sheaf (emptySheafed A).sheaf).symm (⟨f.hom.c⟩)) :=
  underlying_map_pullback_mate f

end SheafCohomologyExamples.AbelianForgetSheafedSpaceClient
