import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Finite generators of leading monomials

Noetherianity of the monomial ideal gives finitely many polynomials whose
leading monomials divide every leading monomial in an ideal. Monomial division
then shows that these polynomials generate the ideal itself.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v

/-- A polynomial ideal in finitely many variables over a field has finitely many
nonzero members whose leading monomials divide all leading monomials of the ideal. -/
theorem exists_leading_generators {σ : Type u} [Finite σ]
    {F : Type v} [Field F] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ F)) :
    ∃ s : Finset (MvPolynomial σ F),
      (∀ q ∈ s, q ∈ I ∧ q ≠ 0) ∧ ∀ p ∈ I, p ≠ 0 →
        ∃ q ∈ s, m.degree q ≤ m.degree p := by
  classical
  let S : Set (MvPolynomial σ F) := {p | p ∈ I ∧ p ≠ 0}
  let a : MvPolynomial σ F → MvPolynomial σ F := fun p ↦ monomial (m.degree p) 1
  have hj : (Submodule.span (MvPolynomial σ F) (a '' S)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (a '' S)).mp hj
  have hchoose (z : t) : ∃ p ∈ S, a p = z.val := ht z.property
  choose b hb he using hchoose
  let s : Finset (MvPolynomial σ F) := Finset.univ.image b
  refine ⟨s, ?_, ?_⟩
  · intro q hq
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
    exact hb z
  · intro p hp hp0
    have hmem : monomial (m.degree p) (1 : F) ∈
        Ideal.span ((fun d : σ →₀ ℕ ↦ monomial d (1 : F)) '' Set.range (m.degree ∘ b)) := by
      have hinit : a p ∈ Ideal.span (a '' S) :=
        Ideal.subset_span ⟨p, ⟨hp, hp0⟩, rfl⟩
      change a p ∈ Submodule.span (MvPolynomial σ F) (a '' S) at hinit
      rw [hspan] at hinit
      apply (Submodule.span_mono (s := (t : Set (MvPolynomial σ F))) ?_) hinit
      intro z hz
      refine ⟨m.degree (b ⟨z, hz⟩), ⟨⟨z, hz⟩, rfl⟩, ?_⟩
      exact he ⟨z, hz⟩
    obtain ⟨d, ⟨z, rfl⟩, hd⟩ :=
      MvPolynomial.mem_ideal_span_monomial_image.mp hmem (m.degree p) (by simp)
    exact ⟨b z, Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, hd⟩

/-- Unit leading coefficients and divisibility of leading monomials imply ideal generation. -/
theorem span_eq_of_leading_generators {σ : Type u} {R : Type v} [CommRing R]
    (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
    (s : Finset (MvPolynomial σ R)) (hs : ∀ q ∈ s, q ∈ I)
    (hu : ∀ q ∈ s, IsUnit (m.leadingCoeff q))
    (hd : ∀ p ∈ I, p ≠ 0 → ∃ q ∈ s, m.degree q ≤ m.degree p) :
    Ideal.span (s : Set (MvPolynomial σ R)) = I := by
  classical
  apply le_antisymm (Ideal.span_le.mpr hs)
  intro p hp
  obtain ⟨g, r, hpr, _, hr⟩ := m.div_set (B := (s : Set (MvPolynomial σ R))) hu p
  have hg : Finsupp.linearCombination (MvPolynomial σ R)
      (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g ∈ Ideal.span (s : Set _) := by
    apply Submodule.sum_mem
    intro q _
    exact Submodule.smul_mem _ _ (Ideal.subset_span q.property)
  have hri : r ∈ I := by
    have hgi : Finsupp.linearCombination (MvPolynomial σ R)
        (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g ∈ I :=
      (Ideal.span_le.mpr hs) hg
    have he : r = p - Finsupp.linearCombination (MvPolynomial σ R)
        (fun q : (s : Set (MvPolynomial σ R)) ↦ q.val) g := by rw [hpr]; abel
    rw [he]
    exact I.sub_mem hp hgi
  have hr0 : r = 0 := by
    by_contra h
    obtain ⟨q, hq, hqr⟩ := hd r hri h
    exact hr (m.degree r) (m.degree_mem_support h) q hq hqr
  rw [hr0, add_zero] at hpr
  exact hpr ▸ hg

/-- A finite leading-monomial generating set over a field also generates its polynomial ideal. -/
theorem exists_polynomial_generators {σ : Type u} [Finite σ]
    {F : Type v} [Field F] (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ F)) :
    ∃ s : Finset (MvPolynomial σ F),
      Ideal.span (s : Set (MvPolynomial σ F)) = I ∧
      (∀ q ∈ s, q ≠ 0) ∧ ∀ p ∈ I, p ≠ 0 → ∃ q ∈ s, m.degree q ≤ m.degree p := by
  obtain ⟨s, hs, hd⟩ := exists_leading_generators m I
  refine ⟨s, span_eq_of_leading_generators m I s (fun q hq ↦ (hs q hq).1) ?_ hd,
    (fun q hq ↦ (hs q hq).2), hd⟩
  intro q hq
  exact isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr (hs q hq).2)

end

end GroupActions
