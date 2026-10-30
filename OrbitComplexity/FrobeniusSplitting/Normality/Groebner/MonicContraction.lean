import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.InitialBasis
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Adjoin.FG

/-! Monic bases on one coefficient ring for contracted polynomial ideals. -/

open MvPolynomial

namespace FrobeniusSplitting

private theorem degree_coeff_map {σ A B : Type*} [CommRing A] [CommRing B]
    (m : MonomialOrder σ) (f : A →+* B) (hf : Function.Injective f)
    (p : MvPolynomial σ A) : m.degree (map f p) = m.degree p := by
  simp only [MonomialOrder.degree, support_map_of_injective p hf]

private theorem leadingCoeff_coeff_map {σ A B : Type*} [CommRing A] [CommRing B]
    (m : MonomialOrder σ) (f : A →+* B) (hf : Function.Injective f)
    (p : MvPolynomial σ A) : m.leadingCoeff (map f p) = f (m.leadingCoeff p) := by
  simp only [MonomialOrder.leadingCoeff, degree_coeff_map m f hf p, coeff_map]

/-- A monic initial family generates its ideal. -/
theorem span_initial_monic {σ A ι : Type*} [CommRing A] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ A)) (b : ι → MvPolynomial σ A)
    (hb : ∀ i, b i ∈ I) (hm : ∀ i, m.Monic (b i))
    (hi : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree p) :
    Ideal.span (Set.range b) = I := by
  classical
  let H : Ideal (MvPolynomial σ A) := Ideal.span (Set.range b)
  have hHI : H ≤ I := Ideal.span_le.mpr (Set.range_subset_iff.mpr hb)
  apply le_antisymm hHI
  intro p hp
  obtain ⟨g, r, hf, _, hr⟩ := m.div (fun i => (hm i) ▸ isUnit_one) p
  have hc : Finsupp.linearCombination (MvPolynomial σ A) b g ∈ H := by
    rw [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem H fun i _ => H.smul_mem (g i) (Ideal.subset_span ⟨i, rfl⟩)
  have hrI : r ∈ I := by
    have heq : r = p - Finsupp.linearCombination (MvPolynomial σ A) b g := by
      rw [hf, add_sub_cancel_left]
    rw [heq]
    exact I.sub_mem hp (hHI hc)
  have hr0 : r = 0 := by
    by_contra hn
    obtain ⟨i, hdiv⟩ := hi r hrI hn
    exact hr (m.degree r) ((m.degree_mem_support_iff r).mpr hn) i hdiv
  rw [hr0, add_zero] at hf
  exact hf.symm ▸ hc

/-- A finite coefficient enlargement carries a monic basis of the contracted ideal. -/
theorem exists_monic_contraction {σ K : Type*} [Finite σ] [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ _ : S ≤ R,
      ∃ t : Finset (MvPolynomial σ K), ∃ b : t → MvPolynomial σ R,
        (∀ i, map R.val.toRingHom (b i) = (i : MvPolynomial σ K) ∧
          (i : MvPolynomial σ K) ∈ I ∧ m.Monic (b i)) ∧
        Ideal.span (t : Set (MvPolynomial σ K)) = I ∧
        (∀ p ∈ I, p ≠ 0 → ∃ i : t, m.degree (i : MvPolynomial σ K) ≤ m.degree p) ∧
        (∀ p : MvPolynomial σ R, map R.val.toRingHom p ∈ I → p ≠ 0 →
          ∃ i, m.degree (b i) ≤ m.degree p) ∧
        Ideal.span (Set.range b) = I.comap (map R.val.toRingHom) ∧
        (I.comap (map R.val.toRingHom)).map (map R.val.toRingHom) = I := by
  classical
  obtain ⟨t, ht, hi⟩ := exists_initial_monic m I
  let c : Finset K := t.biUnion fun p => p.coeffs
  let R : Subalgebra ℤ K := S ⊔ Algebra.adjoin ℤ (c : Set K)
  have hR : R.FG := hS.sup (Subalgebra.fg_adjoin_finset c)
  have hSR : S ≤ R := le_sup_left
  have hval : Function.Injective R.val.toRingHom := Subtype.val_injective
  have hlift (i : t) : ∃ q : MvPolynomial σ R,
      map R.val.toRingHom q = (i : MvPolynomial σ K) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro z hz
    have hc : z ∈ c := Finset.mem_biUnion.mpr ⟨i, i.property, hz⟩
    have hsub : Algebra.adjoin ℤ (c : Set K) ≤ R := le_sup_right
    have hzR : z ∈ R := hsub (Algebra.subset_adjoin hc)
    exact ⟨⟨z, hzR⟩, rfl⟩
  choose b hb using hlift
  have hmonic (i : t) : m.Monic (b i) := by
    apply hval
    change R.val.toRingHom (m.leadingCoeff (b i)) = R.val.toRingHom 1
    rw [← leadingCoeff_coeff_map m R.val.toRingHom hval, hb]
    exact (ht i i.property).2.trans (map_one R.val.toRingHom).symm
  have hmem (i : t) : b i ∈ I.comap (map R.val.toRingHom) := by
    change map R.val.toRingHom (b i) ∈ I
    rw [hb]
    exact (ht i i.property).1
  have hinit (p : MvPolynomial σ R) (hp : map R.val.toRingHom p ∈ I)
      (hn : p ≠ 0) : ∃ i, m.degree (b i) ≤ m.degree p := by
    have hpn : map R.val.toRingHom p ≠ 0 := by
      intro h
      exact hn ((map_injective R.val.toRingHom hval) (h.trans (map_zero _).symm))
    obtain ⟨i, hit, hdiv⟩ := hi _ hp hpn
    refine ⟨⟨i, hit⟩, ?_⟩
    have hdeg : m.degree (b ⟨i, hit⟩) = m.degree i :=
      (degree_coeff_map m R.val.toRingHom hval _).symm.trans (congrArg m.degree (hb _))
    rw [hdeg]
    rwa [degree_coeff_map m R.val.toRingHom hval] at hdiv
  have hspan : Ideal.span (t : Set (MvPolynomial σ K)) = I := by
    have htspan := span_initial_monic m I (fun i : t => (i : MvPolynomial σ K))
      (fun i => (ht i i.property).1) (fun i => (ht i i.property).2) (by
        intro p hp hn
        obtain ⟨i, hit, hid⟩ := hi p hp hn
        exact ⟨⟨i, hit⟩, hid⟩)
    have hrange : Set.range (fun i : t => (i : MvPolynomial σ K)) =
        (t : Set (MvPolynomial σ K)) := by
      ext p
      exact ⟨fun ⟨i, hi⟩ => hi ▸ i.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
    rw [hrange] at htspan
    exact htspan
  have hmap : (I.comap (map R.val.toRingHom)).map (map R.val.toRingHom) = I := by
    apply le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl)
    apply le_trans hspan.symm.le
    apply Ideal.span_le.mpr
    intro p hp
    let i : t := ⟨p, hp⟩
    have heq : map R.val.toRingHom (b i) = p := hb i
    exact heq ▸ (Ideal.mem_map_of_mem (map R.val.toRingHom) (hmem i))
  refine ⟨R, hR, hSR, t, b, ?_, hspan, ?_, hinit, ?_, hmap⟩
  · exact fun i => ⟨hb i, (ht i i.property).1, hmonic i⟩
  · intro p hp hn
    obtain ⟨i, hit, hid⟩ := hi p hp hn
    exact ⟨⟨i, hit⟩, hid⟩
  · exact span_initial_monic m _ b hmem hmonic hinit

end FrobeniusSplitting
