import OrbitComplexity.FrobeniusSplitting.Normality.GenericFibres
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Group.Int.Units

/-!
# Arithmetic fibers and generic surjectivity

A field of finite type over the integers is finite. The maximal points of a finite-type integer
algebra therefore have prime characteristic and are dense. Surjectivity of a finite algebra map
on these quotient fibers implies surjectivity after generic localization.
-/

namespace FrobeniusSplitting

open AlgebraicGeometry Topology TopologicalSpace

private theorem coker_mod_subsingleton {A M N : Type*} [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (f : M →ₗ[A] N) (J : Ideal A)
    (hf : ∀ n : N, ∃ m : M, n - f m ∈ (J • ⊤ : Submodule A N)) :
    Subsingleton ((N ⧸ f.range) ⧸ (J • ⊤ : Submodule A (N ⧸ f.range))) := by
  let q := f.range.mkQ
  have hq : Function.Surjective q := f.range.mkQ_surjective
  have hc : (J • ⊤ : Submodule A (N ⧸ f.range)).comap q = ⊤ := by
    rw [Submodule.comap_smul_top_of_surjective J q hq, Submodule.ker_mkQ]
    apply eq_top_iff.mpr
    intro n _
    obtain ⟨m, hm⟩ := hf n
    have h₁ : n - f m ∈ (J • ⊤ : Submodule A N) ⊔ f.range :=
      (show (J • ⊤ : Submodule A N) ≤ (J • ⊤ : Submodule A N) ⊔ f.range from le_sup_left) hm
    have h₂ : f m ∈ (J • ⊤ : Submodule A N) ⊔ f.range :=
      (show f.range ≤ (J • ⊤ : Submodule A N) ⊔ f.range from le_sup_right) ⟨m, rfl⟩
    simpa only [sub_add_cancel] using Submodule.add_mem _ h₁ h₂
  have ht : (J • ⊤ : Submodule A (N ⧸ f.range)) = ⊤ := by
    apply eq_top_iff.mpr
    intro n _
    obtain ⟨m, rfl⟩ := hq n
    change m ∈ (J • ⊤ : Submodule A (N ⧸ f.range)).comap q
    rw [hc]
    trivial
  rw [ht]
  infer_instance

universe u v

/-- Surjectivity modulo dense base primes implies generic surjectivity of a linear map. -/
theorem surjective_generic_of_mod {R A : Type u} {M N : Type v}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [Module R M] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hf : ∀ p ∈ D, ∀ n : N, ∃ m : M,
      n - f m ∈ ((p.asIdeal.map (algebraMap R A)) • ⊤ : Submodule A N)) :
    Function.Surjective (LocalizedModule.map (nonZeroDivisors R) (f.restrictScalars R)) :=
  surjective_localizedMap_of_dense f D hD fun p hp ↦
    coker_mod_subsingleton f _ (hf p hp)

/-- The ring of integers is Jacobson. -/
instance intJacobson : IsJacobsonRing ℤ := by
  have hj : (⊥ : Ideal ℤ).jacobson = ⊥ := by
    apply le_antisymm
    · intro x hx
      change x = 0
      have hu := Ideal.mem_jacobson_bot.mp hx 3
      rcases Int.isUnit_iff.mp hu with h | h <;> omega
    · exact bot_le
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hp
  by_cases hP : P = ⊥
  · simpa only [hP] using hj
  · have : P.IsMaximal := hp.isMaximal hP
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field of finite type over the integers has prime characteristic. -/
theorem prime_char_finiteType_int (F : Type*) [Field F] [Algebra.FiniteType ℤ F] :
    (ringChar F).Prime := by
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have : Algebra.IsIntegral ℤ F := inferInstance
  apply CharP.char_prime_of_ne_zero F
  intro h
  have : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp h
  exact Int.not_isField (isField_of_isIntegral_of_isField
    (FaithfulSMul.algebraMap_injective ℤ F) (Field.toIsField F))


/-- A field of finite type over the integers is finite. -/
theorem finite_of_finiteType_int (F : Type*) [Field F] [Algebra.FiniteType ℤ F] :
    Finite F := by
  have hp := prime_char_finiteType_int F
  have : NeZero (ringChar F) := ⟨hp.ne_zero⟩
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have : Module.Finite (ZMod (ringChar F)) F :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod (ringChar F)) F
  exact Module.finite_of_finite (ZMod (ringChar F))


/-- Closed points of a finite-type integer algebra have prime characteristic and are dense. -/
theorem dense_prime_char_points (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R] :
    Dense {p : PrimeSpectrum R |
      p.asIdeal.IsMaximal ∧ (ringChar (R ⧸ p.asIdeal)).Prime} := by
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ) (B := R)
  have hd : Dense (closedPoints (PrimeSpectrum R)) :=
    dense_iff_closure_eq.mpr closure_closedPoints
  apply hd.mono
  intro p hp
  have : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp
  refine ⟨inferInstance, ?_⟩
  let : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  have hft : Algebra.FiniteType ℤ (R ⧸ p.asIdeal) := Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ ℤ p.asIdeal) Ideal.Quotient.mk_surjective
  have : Finite (R ⧸ p.asIdeal) :=
    @finite_of_finiteType_int (R ⧸ p.asIdeal) inferInstance hft
  exact CharP.prime_ringChar (R ⧸ p.asIdeal)


/-- Surjectivity modulo dense base primes gives generic surjectivity of an algebra map. -/
theorem generic_surjective_algebra {R A B : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hf : ∀ p ∈ D, ∀ b : B, ∃ a : A,
      Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) b =
        Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) (algebraMap A B a)) :
    Function.Surjective (LocalizedModule.map (nonZeroDivisors R)
      ((Algebra.linearMap A B).restrictScalars R)) := by
  apply surjective_generic_of_mod (Algebra.linearMap A B) D hD
  intro p hp b
  obtain ⟨a, ha⟩ := hf p hp b
  refine ⟨a, ?_⟩
  rw [Ideal.smul_top_eq_map]
  change b - algebraMap A B a ∈
    (p.asIdeal.map (algebraMap R A)).map (algebraMap A B)
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ha

/-- Surjectivity on closed fibers of prime characteristic gives generic surjectivity
for an algebra over a finite-type integer domain. -/
theorem surjective_generic_closed_fibers {R A B : Type u}
    [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal → (ringChar (R ⧸ p.asIdeal)).Prime →
      ∀ b : B, ∃ a : A,
      Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) b =
        Ideal.Quotient.mk (p.asIdeal.map (algebraMap R B)) (algebraMap A B a)) :
    Function.Surjective (LocalizedModule.map (nonZeroDivisors R)
      ((Algebra.linearMap A B).restrictScalars R)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  exact generic_surjective_algebra _ (dense_prime_char_points R)
    fun p hp b ↦ hf p hp.1 hp.2 b

end FrobeniusSplitting
