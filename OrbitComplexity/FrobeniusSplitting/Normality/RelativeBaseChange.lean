import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Base change of relative scheme gluing
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- Cartesian affine comparisons glue to a cartesian comparison over the base schemes. -/
theorem isPullback_relativeGluing {S Y Z : Scheme.{u}} (𝒰 : S.OpenCover)
    [Category 𝒰.I₀] [𝒰.LocallyDirected] [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
    (d : Scheme.Cover.RelativeGluingData 𝒰) (a : S ⟶ Z) (b : d.glued ⟶ Y)
    (c : Y ⟶ Z)
    (h : ∀ i, IsPullback (d.natTrans.app i) (colimit.ι d.functor i ≫ b)
      (𝒰.f i ≫ a) c) : IsPullback d.toBase b a c := by
  apply Scheme.isPullback_of_openCover d.toBase b a c 𝒰
  intro i
  let e := (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
  apply (h i).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change d.natTrans.app i = e.hom ≫ pullback.snd _ _
    exact (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd.symm
  · change colimit.ι d.functor i ≫ b = e.hom ≫ pullback.fst _ _ ≫ b
    rw [← Category.assoc]
    exact congrArg (fun f ↦ f ≫ b)
      (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_fst.symm
  · change (𝒰.f i ≫ a) ≫ 𝟙 Z = 𝟙 (𝒰.X i) ≫ (𝒰.f i ≫ a)
    rw [Category.comp_id, Category.id_comp]
  · change c ≫ 𝟙 Z = 𝟙 Y ≫ c
    rw [Category.comp_id, Category.id_comp]

end FrobeniusSplitting
