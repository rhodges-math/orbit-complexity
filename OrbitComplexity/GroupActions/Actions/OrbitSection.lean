import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Fibre trivialization from an orbit section

An equivariant morphism becomes a product with its fibre after pullback along a regular
section of an orbit map. The construction uses the group action and the pullback universal property.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {H X Y Z : C} [GrpObj H] [ModObj H X] [ModObj H Y]
  (f : X ⟶ Y) [IsModHom H f] (y : 𝟙_ C ⟶ Y) (c : Z ⟶ Y) (s : Z ⟶ H)
  (hc : c = lift s (toUnit Z ≫ y) ≫ γ[H, Y])

include hc in
private theorem untwist_condition {A : C} (a : A ⟶ Z) (x : A ⟶ X)
    (hx : x ≫ f = a ≫ c) : ((a ≫ s)⁻¹ • x) ≫ f = toUnit A ≫ y := by
  change c = s • (toUnit Z ≫ y) at hc
  rw [IsModHom.map_smul, hx, hc, ModObj.comp_smul]
  simp only [comp_toUnit_assoc, inv_smul_smul]

include hc in
private theorem twist_condition {A : C} (a : A ⟶ Z) (x : A ⟶ X)
    (hx : x ≫ f = toUnit A ≫ y) : ((a ≫ s) • x) ≫ f = a ≫ c := by
  change c = s • (toUnit Z ≫ y) at hc
  rw [IsModHom.map_smul, hx, hc, ModObj.comp_smul]
  simp only [comp_toUnit_assoc]

variable [HasPullback f c] [HasPullback f y]

omit [GrpObj H] [ModObj H X] [ModObj H Y] [IsModHom H f] [HasPullback f c] in
private theorem fiber_condition :
    pullback.fst f y ≫ f = toUnit (pullback f y) ≫ y :=
  (pullback.condition (f := f) (g := y)).trans
    (congrArg (fun k : pullback f y ⟶ 𝟙_ C => k ≫ y) (toUnit_unique _ _))

private def forwardF : pullback f c ⟶ pullback f y :=
  pullback.lift (((pullback.snd f c ≫ s)⁻¹) • pullback.fst f c)
    (toUnit (pullback f c))
    (untwist_condition f y c s hc (pullback.snd f c) (pullback.fst f c)
      (pullback.condition (f := f) (g := c)))

private def forward : pullback f c ⟶ Z ⊗ pullback f y :=
  lift (pullback.snd f c) (forwardF f y c s hc)

private def backward : Z ⊗ pullback f y ⟶ pullback f c :=
  pullback.lift ((fst Z (pullback f y) ≫ s) •
    (snd Z (pullback f y) ≫ pullback.fst f y)) (fst Z (pullback f y))
    (twist_condition f y c s hc (fst Z (pullback f y))
      (snd Z (pullback f y) ≫ pullback.fst f y) (by
        rw [Category.assoc, fiber_condition f y, comp_toUnit_assoc]))

/-- A regular section of an orbit map trivializes an equivariant fibre family. -/
def orbitSectionIso : pullback f c ≅ Z ⊗ pullback f y where
  hom := forward f y c s hc
  inv := backward f y c s hc
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [forward, backward, forwardF, ModObj.comp_smul]
    · simp [forward, backward]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [forward, backward]
    · apply pullback.hom_ext
      · simp [forward, backward, forwardF, ModObj.comp_smul, GrpObj.comp_inv]
      · exact toUnit_unique _ _

/-- The orbit-section isomorphism preserves the parameter projection. -/
theorem orbitSectionIso_hom_fst : (orbitSectionIso f y c s hc).hom ≫ fst Z (pullback f y) =
    pullback.snd f c := by
  simp [orbitSectionIso, forward]

/-- The inverse orbit-section isomorphism preserves the parameter projection. -/
theorem orbitSectionIso_inv_snd : (orbitSectionIso f y c s hc).inv ≫ pullback.snd f c =
    fst Z (pullback f y) := by
  simp [orbitSectionIso, backward]

/-- The inverse orbit-section isomorphism acts by the given section. -/
theorem orbitSectionIso_inv_fst : (orbitSectionIso f y c s hc).inv ≫ pullback.fst f c =
    lift (fst Z (pullback f y) ≫ s) (snd Z (pullback f y) ≫ pullback.fst f y) ≫ γ[H, X] := by
  simp [orbitSectionIso, backward, CategoryTheory.Hom.smul_def]

/-- The orbit-section isomorphism acts by the inverse section. -/
theorem orbitSectionIso_hom_snd_fst :
    (orbitSectionIso f y c s hc).hom ≫ snd Z (pullback f y) ≫ pullback.fst f y =
      lift ((pullback.snd f c ≫ s)⁻¹) (pullback.fst f c) ≫ γ[H, X] := by
  simp [orbitSectionIso, forward, forwardF, CategoryTheory.Hom.smul_def]

end

end GroupActions
