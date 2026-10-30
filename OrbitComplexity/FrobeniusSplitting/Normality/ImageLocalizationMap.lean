import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ImageLocalization

/-!
# Image Localization Map

Commuting localization maps induce localization maps on their images.
-/

namespace FrobeniusSplitting

variable {R M A B F : Type*}
    [CommRing R] [CommRing M] [CommRing A] [CommRing B] [CommRing F]
    [Algebra R M] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra M F] [Algebra R F] [IsScalarTower R M F]

/-- A commuting localization square induces a localization of its image algebras. -/
theorem localization_image_of_commutes (q : M →ₐ[R] A) (g : M)
    [IsLocalization.Away g F] [IsLocalization.Away (q g) B]
    (r : F →ₐ[R] B)
    (hcomm : r.comp (IsScalarTower.toAlgHom R M F) =
      (IsScalarTower.toAlgHom R A B).comp q) :
    ∃ f : q.range →ₐ[R] r.range,
      (∀ a, (f a : B) = algebraMap A B (a : A)) ∧
      letI : Algebra q.range r.range := f.toAlgebra
      IsLocalization.Away (⟨q g, ⟨g, rfl⟩⟩ : q.range) r.range := by
  let ψ := IsLocalization.Away.mapₐ F B q g
  have hr : r = ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    change r.comp (IsScalarTower.toAlgHom R M F) =
      ψ.comp (IsScalarTower.toAlgHom R M F)
    rw [hcomm]
    ext m
    change algebraMap A B (q m) = ψ (algebraMap M F m)
    simp [ψ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]
  subst r
  exact localization_image (F := F) q g

end FrobeniusSplitting
