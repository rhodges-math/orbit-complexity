import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The ideal of a scheme-theoretic closed intersection -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- The raw fibre product of two closed immersions has precisely the sum
of their ideal sheaves, without reducedness or normality assumptions. -/
theorem closed_intersection_ker {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g] :
    (pullback.fst f g ≫ f).ker = f.ker ⊔ g.ker := by
  let J := f.ker ⊔ g.ker
  let i := J.subschemeι
  have hi : i.ker = J := J.ker_subschemeι
  have hf : f.ker ≤ i.ker := hi.symm ▸ le_sup_left
  have hg : g.ker ≤ i.ker := hi.symm ▸ le_sup_right
  let a := IsClosedImmersion.lift f i hf
  let b := IsClosedImmersion.lift g i hg
  have ha : a ≫ f = i := IsClosedImmersion.lift_fac f i hf
  have hb : b ≫ g = i := IsClosedImmersion.lift_fac g i hg
  let q := pullback.lift a b (ha.trans hb.symm)
  have hq : q ≫ (pullback.fst f g ≫ f) = i := by
    rw [← Category.assoc, pullback.lift_fst, ha]
  apply le_antisymm
  · have h := Scheme.Hom.le_ker_comp q (pullback.fst f g ≫ f)
    rw [hq, hi] at h
    exact h
  · apply sup_le
    · exact Scheme.Hom.le_ker_comp (pullback.fst f g) f
    · rw [pullback.condition]
      exact Scheme.Hom.le_ker_comp (pullback.snd f g) g


end FrobeniusSplitting
