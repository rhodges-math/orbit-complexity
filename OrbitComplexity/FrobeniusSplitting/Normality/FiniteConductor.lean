import OrbitComplexity.FrobeniusSplitting.Normality.Conductor
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Support

/-!
# Conductors of finite intermediate algebras

The conductor in the base ring is the annihilator of the quotient module of the
extension by the base ring. Its zero locus is the support of that quotient when
the extension is finite. If the extension embeds in a localization of the base,
one denominator belongs to the conductor.

## Main results

* `FrobeniusSplitting.conductor_comap_eq_annihilator`: the conductor as an annihilator.
* `FrobeniusSplitting.mem_support_quotient_iff`: support detected by the conductor.
* `FrobeniusSplitting.exists_mem_conductor`: a common denominator in the conductor.
* `FrobeniusSplitting.surjective_of_quotientMap`: lifting surjectivity modulo an
  ideal contained in the base image.

## References

* M. Brion and S. Kumar, *Frobenius Splitting Methods in Geometry and Representation
  Theory*, Progress in Mathematics 231, Birkhäuser (2005), Proposition 1.2.5.
-/

namespace FrobeniusSplitting

variable {A B K : Type*} [CommRing A] [CommRing B] [CommRing K]
  [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
  [FaithfulSMul B K]

/-- The conductor in the base ring annihilates the quotient of the algebra by the base ring. -/
theorem conductor_comap_eq_annihilator :
    (conductor A (1 : B)).comap (algebraMap A B) =
      Module.annihilator A (B ⧸ (⊥ : Subalgebra A B).toSubmodule) := by
  ext a
  rw [Submodule.annihilator_quotient]
  change algebraMap A B a ∈ conductor A (1 : B) ↔
    a ∈ (⊥ : Subalgebra A B).toSubmodule.colon Set.univ
  rw [mem_conductor_iff, Submodule.mem_colon, Algebra.adjoin_singleton_one]
  simp only [Set.mem_univ, forall_const]
  change (∀ b : B, algebraMap A B a * b ∈ (⊥ : Subalgebra A B)) ↔
    ∀ b : B, a • b ∈ (⊥ : Subalgebra A B)
  simp only [Algebra.smul_def]

/-- The failure of the base algebra to fill a finite algebra is supported on the conductor. -/
theorem mem_support_quotient_iff [Module.Finite A B] (prime : PrimeSpectrum A) :
    prime ∈ Module.support A (B ⧸ (⊥ : Subalgebra A B).toSubmodule) ↔
      (conductor A (1 : B)).comap (algebraMap A B) ≤ prime.asIdeal := by
  rw [Module.mem_support_iff_of_finite, ← conductor_comap_eq_annihilator]

/-- A finite intermediate algebra in a localization has a denominator in its conductor. -/
theorem exists_mem_conductor (M : Submonoid A) [IsLocalization M K]
    [Module.Finite A B] : ∃ s : M, algebraMap A B s ∈ conductor A (1 : B) := by
  obtain ⟨generators, hgenerators⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples M generators (algebraMap B K)
  let integral := (⊥ : Subalgebra A B).toSubmodule.comap
    ((s : A) • LinearMap.id : B →ₗ[A] B)
  have hspan : Submodule.span A (generators : Set B) ≤ integral := by
    apply Submodule.span_le.2
    intro b hb
    change (s : A) • b ∈ (⊥ : Subalgebra A B)
    obtain ⟨a, ha⟩ := hs b hb
    refine ⟨a, ?_⟩
    apply FaithfulSMul.algebraMap_injective B K
    exact (IsScalarTower.algebraMap_apply A B K a).symm.trans
      (ha.trans ((IsScalarTower.toAlgHom A B K).toLinearMap.map_smul (s : A) b).symm)
  refine ⟨s, ?_⟩
  rw [mem_conductor_iff, Algebra.adjoin_singleton_one]
  intro b
  have hb : b ∈ integral := hspan (by rw [hgenerators]; trivial)
  change (s : A) • b ∈ (⊥ : Subalgebra A B) at hb
  change algebraMap A B (s : A) * b ∈ (⊥ : Subalgebra A B)
  rwa [Algebra.smul_def] at hb

/-- Surjectivity modulo an ideal contained in the base image lifts to surjectivity. -/
theorem surjective_of_quotientMap {R S : Type*} [CommRing R] [CommRing S]
    (morphism : R →+* S) (ideal : Ideal S)
    (hideal : (ideal : Set S) ⊆ Set.range morphism)
    (hquotient : Function.Surjective (Ideal.quotientMap ideal morphism le_rfl)) :
    Function.Surjective morphism := by
  intro b
  obtain ⟨a, ha⟩ := hquotient (Ideal.Quotient.mk ideal b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨c, hc⟩ := hideal ha
  refine ⟨a - c, ?_⟩
  rw [morphism.map_sub, hc]
  ring

end FrobeniusSplitting
