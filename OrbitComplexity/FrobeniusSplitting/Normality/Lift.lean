import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Lifting normalization into normal rings

The fraction-field embedding of a domain into an ambient field maps its normalization
into every subring that contains the original domain and is integrally closed in that
field. The resulting lift is an injective algebra homomorphism.
-/

namespace FrobeniusSplitting

variable (R B F : Type*) [CommRing R] [IsDomain R] [CommRing B] [Field F]
    [Algebra R B] [Algebra R F] [Algebra B F] [IsScalarTower R B F]
    [FaithfulSMul R F] [IsIntegrallyClosedIn B F]

/-- An injective rational map into an integrally closed subring sends every element
of the normalization into that subring. -/
noncomputable def normalizationLift : integralClosure R (FractionRing R) →ₐ[R] B := by
  let φ : integralClosure R (FractionRing R) →ₐ[R] F :=
    (IsFractionRing.liftAlgHom (g := Algebra.ofId R F)
      (FaithfulSMul.algebraMap_injective R F)).comp (integralClosure R (FractionRing R)).val
  have hi (c : integralClosure R (FractionRing R)) : IsIntegral B (φ c) :=
    ((c.2.map (IsFractionRing.liftAlgHom (g := Algebra.ofId R F)
      (FaithfulSMul.algebraMap_injective R F))).tower_top (A := B))
  refine
    { toFun := fun c ↦ IsIntegralClosure.mk' B (φ c) (hi c)
      map_zero' := by
        apply IsIntegralClosure.algebraMap_injective B B F
        simp
      map_one' := by
        apply IsIntegralClosure.algebraMap_injective B B F
        simp
      map_add' := fun c d ↦ by
        apply IsIntegralClosure.algebraMap_injective B B F
        simp [IsIntegralClosure.algebraMap_mk']
      map_mul' := fun c d ↦ by
        apply IsIntegralClosure.algebraMap_injective B B F
        simp [IsIntegralClosure.algebraMap_mk']
      commutes' := fun r ↦ by
        apply IsIntegralClosure.algebraMap_injective B B F
        rw [IsIntegralClosure.algebraMap_mk', φ.commutes,
          IsScalarTower.algebraMap_apply R B F] }

/-- The lift to an integrally closed subring agrees with the rational map in the ambient field. -/
theorem algebraMap_normalizationLift (c : integralClosure R (FractionRing R)) :
    algebraMap B F (normalizationLift R B F c) =
      IsFractionRing.lift (FaithfulSMul.algebraMap_injective R F) (c : FractionRing R) := by
  exact IsIntegralClosure.algebraMap_mk' (R := B) B _
    ((c.2.map (IsFractionRing.liftAlgHom (g := Algebra.ofId R F)
      (FaithfulSMul.algebraMap_injective R F))).tower_top (A := B))

/-- The lift from the normalization into an integrally closed subring is injective. -/
theorem normalizationLift_injective : Function.Injective (normalizationLift R B F) := by
  intro c d h
  apply Subtype.ext
  apply (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R F)).injective
  have heq := congrArg (algebraMap B F) h
  simpa only [algebraMap_normalizationLift] using heq

end FrobeniusSplitting
