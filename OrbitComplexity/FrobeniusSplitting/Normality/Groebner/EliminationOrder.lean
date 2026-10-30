import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Sum.Order
import Mathlib.Basic.Finite.Sum

/-! Lexicographic elimination of an initial block of variables. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ τ R : Type*} [CommRing R]

private instance [Finite σ] [Finite τ] : Finite (τ ⊕ₗ σ) :=
  Finite.of_equiv (τ ⊕ σ) toLex

private theorem retained_injective :
    Function.Injective (Sum.inrₗ : σ → τ ⊕ₗ σ) := Sum.inr_injective

private theorem retained_left (d : σ →₀ ℕ) (y : τ) :
    d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨x, h⟩
  cases h

private theorem retained_right (d : σ →₀ ℕ) (x : σ) :
    d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inrₗ x) = d x :=
  Finsupp.mapDomain_apply_of_injective retained_injective d x

variable [LinearOrder σ] [LinearOrder τ]

private theorem retained_lt_iff (d e : σ →₀ ℕ) :
    toLex (d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) <
      toLex (e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) ↔ toLex d < toLex e := by
  change Finsupp.Lex (· < ·) (· < ·)
    (d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) (e.mapDomain Sum.inrₗ) ↔
      Finsupp.Lex (· < ·) (· < ·) d e
  constructor
  · intro h
    obtain ⟨y | x, hprev, hlt⟩ := h
    · change d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y) <
        e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y) at hlt
      rw [retained_left, retained_left] at hlt
      exact (lt_irrefl 0 hlt).elim
    · refine ⟨x, ?_, ?_⟩
      · intro z hz
        simpa only [retained_right] using hprev (Sum.inrₗ z)
          (Sum.Lex.inr_lt_inr_iff.mpr hz)
      · change d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inrₗ x) <
          e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inrₗ x) at hlt
        simpa only [retained_right] using hlt
  · intro h
    obtain ⟨x, hprev, hlt⟩ := h
    refine ⟨Sum.inrₗ x, ?_, ?_⟩
    · rintro (y | z) hz
      · change d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y) =
          e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y)
        rw [retained_left, retained_left]
      · change d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inrₗ z) =
          e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inrₗ z)
        change Sum.inrₗ z < (Sum.inrₗ x : τ ⊕ₗ σ) at hz
        rw [retained_right, retained_right]
        exact hprev z (Sum.Lex.inr_lt_inr_iff.mp hz)
    · simpa only [retained_right] using hlt

private theorem retained_le_iff (d e : σ →₀ ℕ) :
    toLex (d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) ≤
      toLex (e.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) ↔ toLex d ≤ toLex e := by
  simpa only [not_lt] using not_congr (retained_lt_iff (τ := τ) e d)

variable [Finite τ]

private theorem lex_left_zero_of_le (d e : (τ ⊕ₗ σ) →₀ ℕ)
    (he : ∀ y, e (Sum.inlₗ y) = 0) (hde : toLex d ≤ toLex e) :
    ∀ y, d (Sum.inlₗ y) = 0 := by
  intro y
  apply WellFoundedLT.induction y
  intro y ih
  by_contra hn
  apply (not_lt_of_ge hde)
  change Finsupp.Lex (· < ·) (· < ·) e d
  refine ⟨Sum.inlₗ y, ?_, ?_⟩
  · rintro (z | x) hz
    · change e (Sum.inlₗ z) = d (Sum.inlₗ z)
      change Sum.inlₗ z < (Sum.inlₗ y : τ ⊕ₗ σ) at hz
      rw [he, ih z (Sum.Lex.inl_lt_inl_iff.mp hz)]
    · change Sum.inrₗ x < (Sum.inlₗ y : τ ⊕ₗ σ) at hz
      exact (Sum.Lex.not_inr_lt_inl hz).elim
  · change e (Sum.inlₗ y) < d (Sum.inlₗ y)
    rw [he]
    exact Nat.pos_of_ne_zero hn

variable [Finite σ]

/-- Renaming into the retained block preserves the lexicographic leading exponent. -/
theorem lex_degree_rename (p : MvPolynomial σ R) :
    (MonomialOrder.lex (σ := τ ⊕ₗ σ)).degree
      (rename (Sum.inrₗ : σ → τ ⊕ₗ σ) p) =
        ((MonomialOrder.lex (σ := σ)).degree p).mapDomain Sum.inrₗ := by
  classical
  let m : MonomialOrder σ := MonomialOrder.lex
  let n : MonomialOrder (τ ⊕ₗ σ) := MonomialOrder.lex
  change n.degree (rename Sum.inrₗ p) = (m.degree p).mapDomain Sum.inrₗ
  by_cases hp : p = 0
  · simp [hp]
  apply n.toSyn.injective
  apply le_antisymm
  · apply n.degree_le_iff.mpr
    intro c hc
    rw [support_rename_of_injective retained_injective] at hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact (retained_le_iff (τ := τ) d (m.degree p)).mpr (m.le_degree hd)
  · apply n.le_degree
    rw [support_rename_of_injective retained_injective]
    exact Finset.mem_image.mpr ⟨m.degree p, m.degree_mem_support hp, rfl⟩

/-- A leading exponent in the retained block forces the whole polynomial into that block. -/
theorem lex_rename_of_degree (p : MvPolynomial (τ ⊕ₗ σ) R)
    (hp : ∀ y, (MonomialOrder.lex (σ := τ ⊕ₗ σ)).degree p (Sum.inlₗ y) = 0) :
    rename (Sum.inrₗ : σ → τ ⊕ₗ σ) (killCompl retained_injective p) = p := by
  classical
  have hv : (p.vars : Set (τ ⊕ₗ σ)) ⊆ Set.range (Sum.inrₗ : σ → τ ⊕ₗ σ) := by
    intro z hz
    obtain ⟨d, hd, hzd⟩ := (mem_vars_iff_mem_support z).mp hz
    obtain y | x := z
    · have hzero := lex_left_zero_of_le d _ hp
        ((MonomialOrder.lex (σ := τ ⊕ₗ σ)).le_degree hd) y
      exact ((Finsupp.mem_support_iff.mp hzd) hzero).elim
    · exact ⟨x, rfl⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range p Sum.inrₗ
    retained_injective hv
  rw [← hq, killCompl_rename_app]

end FrobeniusSplitting
