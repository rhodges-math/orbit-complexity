import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentTangent
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite Type Point Tangent Rigidity

A finite-type affine group with one geometric point and zero identity
tangent has trivial coordinate augmentation ideal. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

variable {K Q : Type*} [Field K] [IsAlgClosed K] [CommRing Q]
  [HopfAlgebra K Q] [Algebra.FiniteType K Q]

omit [IsAlgClosed K] in
private theorem FiniteType.aug_le_sq_of_tangent_subsingleton
    (htan : Subsingleton
      (Derivation K Q (Bialgebra.CounitAlgebra K Q K))) :
    Bialgebra.AugmentationIdeal K Q ≤
      (Bialgebra.AugmentationIdeal K Q) ^ 2 := by
  let m := Bialgebra.AugmentationIdeal K Q
  have hdual : Subsingleton (Module.Dual K (Bialgebra.CotangentSpace K Q)) :=
    (Derivation.cotangentLinearEquiv (R := K) (A := Q) (B := K)).toEquiv.subsingleton_congr.mpr htan
  have hcot : Subsingleton (Bialgebra.CotangentSpace K Q) :=
    (Module.subsingleton_dual_iff K).mp hdual
  intro x hx
  let xx : m := ⟨x, hx⟩
  exact (Ideal.toCotangent_eq_zero m xx).mp (Subsingleton.elim _ _)

/-! The augmentation ideal is equal to its square when the identity tangent is zero. -/
omit [IsAlgClosed K] in
/-- Finite-generation rigidity at the counit, given uniqueness of its maximal ideal. -/
theorem FiniteType.bot_of_unique_maximal_and_tangent_zero
    (hmax : ∀ m : Ideal Q, m.IsMaximal →
      m = Bialgebra.AugmentationIdeal K Q)
    (htan : Subsingleton
      (Derivation K Q (Bialgebra.CounitAlgebra K Q K))) :
    Bialgebra.AugmentationIdeal K Q = ⊥ := by
  let m := Bialgebra.AugmentationIdeal K Q
  let : IsNoetherianRing Q := Algebra.FiniteType.isNoetherianRing K Q
  have hfg : (m : Submodule Q Q).FG := IsNoetherian.noetherian _
  have hsq : m ≤ m ^ 2 := FiniteType.aug_le_sq_of_tangent_subsingleton htan
  have hsmul : (m : Submodule Q Q) ≤ m • (m : Submodule Q Q) := by
    simpa only [Ideal.smul_eq_mul, pow_two] using hsq
  have hjac : m ≤ (⊥ : Ideal Q).jacobson := by
    rw [Ideal.jacobson]
    apply le_sInf
    intro a ha
    exact hmax a ha.2 ▸ le_refl m
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m hfg hsmul hjac

/-- Every maximal ideal of a finite-type algebra over an algebraically
closed field is the kernel of a ground-field point. -/
theorem finiteType_maximal_is_ker_point (m : Ideal Q) (hm : m.IsMaximal) :
    ∃ p : Q →ₐ[K] K, RingHom.ker p.toRingHom = m := by
  let : Field (Q ⧸ m) := Ideal.Quotient.field m
  let : Algebra K (Q ⧸ m) := Ideal.Quotient.algebra K
  let : Algebra.FiniteType K (Q ⧸ m) := Algebra.FiniteType.quotient K m
  let : Module.Finite K (Q ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing K (Q ⧸ m)
  let p : Q →ₐ[K] K := (IsAlgClosed.lift : (Q ⧸ m) →ₐ[K] K).comp
    (Ideal.Quotient.mkₐ K m)
  refine ⟨p, ?_⟩
  have hp : Function.Surjective p := by
    intro k
    refine ⟨algebraMap K Q k, ?_⟩
    exact p.commutes k
  have hk : (RingHom.ker p.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective p.toRingHom hp
  apply (hm.eq_of_le hk.ne_top ?_).symm
  intro x hx
  change p x = 0
  change (IsAlgClosed.lift : (Q ⧸ m) →ₐ[K] K)
    ((Ideal.Quotient.mkₐ K m) x) = 0
  have hqx : (Ideal.Quotient.mkₐ K m) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hqx, map_zero]

/-- A finite-type affine group over an algebraically closed field with
only the identity rational point and zero identity tangent is trivial
as a scheme. -/
theorem FiniteType.aug_eq_bot_of_point_and_tangent_zero
    (hpoint : ∀ p : Q →ₐ[K] K, p = Bialgebra.counitAlgHom K Q)
    (htan : Subsingleton
      (Derivation K Q (Bialgebra.CounitAlgebra K Q K))) :
    Bialgebra.AugmentationIdeal K Q = ⊥ := by
  apply FiniteType.bot_of_unique_maximal_and_tangent_zero (K := K) (Q := Q) ?_ htan
  intro m hm
  obtain ⟨p, hp⟩ := finiteType_maximal_is_ker_point (K := K) m hm
  rw [hpoint p] at hp
  exact hp.symm

end ReductiveGroups
