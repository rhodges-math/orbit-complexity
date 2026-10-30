import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.RelativeModels

/-!
# Pushout Products

Ring pushout elements are finite sums of products from the two source rings.
-/

open CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u

/-- A ring pushout expresses each target element using finitely many source factors. -/
theorem exists_pushout_product_sum_of_hom {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : A →+* C) (p : B →+* D) (q : C →+* D)
    (hpush : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom p) (CommRingCat.ofHom q)) (d : D) :
    ∃ (n : ℕ) (x : Fin n → B) (y : Fin n → C), d = ∑ j, p (x j) * q (y j) := by
  have hcomm : p.comp f = q.comp g := by
    apply RingHom.ext
    intro a
    exact congrArg (fun t ↦ t.hom a) hpush.w
  let : Algebra A B := f.toAlgebra
  let : Algebra A C := g.toAlgebra
  let : Algebra B D := p.toAlgebra
  let : Algebra C D := q.toAlgebra
  let : Algebra A D := (p.comp f).toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a ↦
    RingHom.congr_fun hcomm a
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp hpush
  exact exists_pushout_product_sum (T := A) (U := B) (V := C) d

end FrobeniusSplitting
