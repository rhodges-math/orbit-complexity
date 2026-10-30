import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.InitialBasis
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.StandardMonomials
import Mathlib.RingTheory.Adjoin.FG

/-! Free arithmetic models of polynomial quotients over one coefficient ring. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ K η : Type*} [Field K] [Finite σ] [Finite η]

omit [Finite σ] in
private theorem degree_map_injective {R A : Type*} [CommRing R] [CommRing A]
    (m : MonomialOrder σ) (ρ : R →+* A) (hρ : Function.Injective ρ)
    (f : MvPolynomial σ R) : m.degree (map ρ f) = m.degree f := by
  simp only [MonomialOrder.degree, support_map_of_injective f hρ]

/-- Finitely many polynomial quotients become free over one enlarged coefficient ring. -/
theorem exists_free_polynomial_models (S : Subalgebra ℤ K) (hS : S.FG)
    (m : MonomialOrder σ) (I : η → Ideal (MvPolynomial σ S)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      ∀ i, Module.Free R (MvPolynomial σ R ⧸
        (I i).map (map (Subalgebra.inclusion hSR).toRingHom)) := by
  classical
  let := Fintype.ofFinite η
  let J (i : η) : Ideal (MvPolynomial σ K) :=
    (I i).map (map (algebraMap S K))
  choose t ht hd using fun i => exists_initial_monic m (J i)
  have hex : ∀ (i : η) (j : t i), ∃ c : I i →₀ MvPolynomial σ K,
      (c.sum fun a q => q * map (algebraMap S K) (a : MvPolynomial σ S)) =
        (j : MvPolynomial σ K) := by
    intro i j
    have hj := (ht i j j.property).1
    change (j : MvPolynomial σ K) ∈
      Ideal.span ((map (algebraMap S K)) '' (I i : Set (MvPolynomial σ S))) at hj
    have hset : ((map (algebraMap S K)) '' (I i : Set (MvPolynomial σ S))) =
        Set.range (fun a : I i => map (algebraMap S K) (a : MvPolynomial σ S)) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, rfl⟩
    rw [hset] at hj
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp
      (R := MvPolynomial σ K)
      (v := fun a : I i => map (algebraMap S K) (a : MvPolynomial σ S))).mp hj
    exact ⟨c, by simpa only [smul_eq_mul] using hc⟩
  choose c hc using hex
  let C : Finset K := Finset.univ.biUnion fun i =>
    (t i).attach.biUnion fun j => (c i j).support.biUnion fun a => (c i j a).coeffs
  let R : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ (C : Set K)
  have hR : R.FG := hS.sup (Subalgebra.fg_adjoin_finset C)
  have hSR : S ≤ R := le_sup_left
  let τ : S →+* R := (Subalgebra.inclusion hSR).toRingHom
  let ρ : R →+* K := R.val.toRingHom
  have hcomp : ρ.comp τ = algebraMap S K := rfl
  have hmap (a : MvPolynomial σ S) :
      map ρ (map τ a) = map (algebraMap S K) a := by
    rw [map_map, hcomp]
  have hlift : ∀ (i : η) (j : t i) (a : I i),
      ∃ q : MvPolynomial σ R, map ρ q = c i j a := by
    intro i j a
    apply mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    by_cases ha : a ∈ (c i j).support
    · have hxC : x ∈ C := Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_attach _ _, Finset.mem_biUnion.mpr ⟨a, ha, hx⟩⟩⟩
      exact ⟨⟨x, (show Algebra.adjoin ℤ (C : Set K) ≤ R from le_sup_right)
        (Algebra.subset_adjoin hxC)⟩, rfl⟩
    · have hz : c i j a = 0 := Finsupp.notMem_support_iff.mp ha
      simp only [hz, coeffs_zero, Finset.coe_empty, Set.mem_empty_iff_false] at hx
  choose q hq using hlift
  let b (i : η) (j : t i) : MvPolynomial σ R :=
    ∑ a ∈ (c i j).support, q i j a * map τ (a : MvPolynomial σ S)
  have hbmap (i : η) (j : t i) : map ρ (b i j) = (j : MvPolynomial σ K) := by
    simp only [b, map_sum, map_mul, hq, hmap]
    exact hc i j
  have hbmem (i : η) (j : t i) : b i j ∈ (I i).map (map τ) := by
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ a.property)
  have hbmonic (i : η) (j : t i) : m.Monic (b i j) := by
    apply Subtype.val_injective
    change ρ (m.leadingCoeff (b i j)) = ρ 1
    rw [map_one]
    have hdeg := degree_map_injective m ρ Subtype.val_injective (b i j)
    have h := (ht i j j.property).2
    change (j : MvPolynomial σ K).coeff (m.degree (j : MvPolynomial σ K)) = 1 at h
    rw [← hbmap i j, hdeg, coeff_map] at h
    exact h
  refine ⟨R, hR, hSR, fun i => free_quotient_of_initial_monic m _ (b i)
    (hbmem i) (hbmonic i) ?_⟩
  intro f hf hn
  have hmem : map ρ f ∈ J i := by
    have h := Ideal.mem_map_of_mem (map ρ) hf
    rw [Ideal.map_map] at h
    have hmaps : (map ρ).comp (map τ) = map (algebraMap S K) :=
      RingHom.ext hmap
    rw [hmaps] at h
    exact h
  have hne : map ρ f ≠ 0 := fun h =>
    hn (map_injective ρ Subtype.val_injective (by simpa only [map_zero] using h))
  obtain ⟨j, hj, hdegree⟩ := hd i (map ρ f) hmem hne
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [degree_map_injective m ρ Subtype.val_injective f] at hdegree
  have heq := degree_map_injective m ρ Subtype.val_injective (b i ⟨j, hj⟩)
  rw [hbmap] at heq
  exact heq ▸ hdegree

end FrobeniusSplitting
