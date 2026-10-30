import Batteries.Tactic.Lint
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Image Localization

Images of ring homomorphisms retain principal localization structures.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {R M A B : Type*} [CommRing R] [CommRing M] [CommRing A] [CommRing B]
    [Algebra R M] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The image of a localized algebra map is the localization of the image algebra. -/
theorem localization_image {F : Type*} [CommRing F] [Algebra M F] [Algebra R F]
    [IsScalarTower R M F] (q : M →ₐ[R] A) (g : M)
    [IsLocalization.Away g F] [IsLocalization.Away (q g) B] :
    let ψ := IsLocalization.Away.mapₐ F B q g
    ∃ f : q.range →ₐ[R] ψ.range,
      (∀ a, (f a : B) = algebraMap A B (a : A)) ∧
      letI : Algebra q.range ψ.range := f.toAlgebra
      IsLocalization.Away (⟨q g, ⟨g, rfl⟩⟩ : q.range) ψ.range := by
  let ψ := IsLocalization.Away.mapₐ F B q g
  let I := q.range
  let z : I := ⟨q g, ⟨g, rfl⟩⟩
  let L := Localization.Away z
  have : IsLocalization.Away (I.val z) B := by
    change IsLocalization.Away (q g) B
    infer_instance
  have : IsLocalization.Away (q.rangeRestrict g) L := by
    change IsLocalization.Away z (Localization.Away z)
    infer_instance
  let η := IsLocalization.Away.mapₐ L B I.val z
  let ψ₀ := IsLocalization.Away.mapₐ F L q.rangeRestrict g
  have hη : Function.Injective η :=
    IsLocalization.Away.mapₐ_injective_of_injective
      (f := I.val) (Aₚ := L) (Bₚ := B) z Subtype.val_injective
  have hψ₀ : Function.Surjective ψ₀ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective
      (f := q.rangeRestrict) (Aₚ := F) (Bₚ := L) g q.rangeRestrict_surjective
  have hcomp : η.comp ψ₀ = ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    ext m
    change η (ψ₀ (algebraMap M F m)) = ψ (algebraMap M F m)
    simp [η, ψ₀, ψ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]
    change η (algebraMap I L (q.rangeRestrict m)) = algebraMap A B (q m)
    simp only [η, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  have hrange : η.range = ψ.range := by
    rw [← hcomp, AlgHom.range_comp, (AlgHom.range_eq_top ψ₀).mpr hψ₀, Algebra.map_top]
  let t : L →ₐ[R] ψ.range := η.codRestrict ψ.range fun l ↦ hrange ▸ ⟨l, rfl⟩
  have ht : Function.Bijective t := by
    constructor
    · intro a b h
      exact hη (congrArg Subtype.val h)
    · intro b
      obtain ⟨l, hl⟩ : (b : B) ∈ η.range := hrange.symm ▸ b.property
      exact ⟨l, Subtype.ext hl⟩
  let f : I →ₐ[R] ψ.range := t.comp (IsScalarTower.toAlgHom R I L)
  refine ⟨f, ?_, ?_⟩
  · intro a
    change η (algebraMap I L a) = algebraMap A B (a : A)
    simp [η, IsLocalization.Away.mapₐ, IsLocalization.Away.map]
  · let : Algebra I ψ.range := f.toAlgebra
    let e : L ≃ₐ[I] ψ.range :=
      { (AlgEquiv.ofBijective t ht).toRingEquiv with commutes' := fun _ ↦ rfl }
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers z) e

end FrobeniusSplitting
