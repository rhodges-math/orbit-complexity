import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.EliminationOrder
import OrbitComplexity.FrobeniusSplitting.Normality.Models.StandardInclusion

/-! Polynomial image inclusions split by a monic elimination basis. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ τ R : Type*} [CommRing R]

private theorem retained_injective :
    Function.Injective (Sum.inrₗ : σ → τ ⊕ₗ σ) := Sum.inr_injective

/-- The quotient inclusion induced by retaining the second block of variables. -/
noncomputable def eliminationQuotientMap (J : Ideal (MvPolynomial (τ ⊕ₗ σ) R)) :
    (MvPolynomial σ R ⧸ J.comap (rename Sum.inrₗ).toRingHom) →ₐ[R]
      (MvPolynomial (τ ⊕ₗ σ) R ⧸ J) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R J).comp (rename Sum.inrₗ))
    (fun _ hp => Ideal.Quotient.eq_zero_iff_mem.mpr hp)

/-- The quotient inclusion is induced by the original polynomial renaming. -/
theorem eliminationQuotientMap_mk (J : Ideal (MvPolynomial (τ ⊕ₗ σ) R))
    (p : MvPolynomial σ R) :
    eliminationQuotientMap J (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk J (rename Sum.inrₗ p) := rfl

/-- A monic elimination basis gives a module retraction of the image quotient inclusion. -/
theorem split_elimination_quotient {κ : Type*} [LinearOrder σ] [LinearOrder τ]
    [Finite σ] [Finite τ] (J : Ideal (MvPolynomial (τ ⊕ₗ σ) R))
    (b : κ → MvPolynomial (τ ⊕ₗ σ) R) (hb : ∀ i, b i ∈ J)
    (hm : ∀ i, (MonomialOrder.lex (σ := τ ⊕ₗ σ)).Monic (b i))
    (hi : ∀ p ∈ J, p ≠ 0 → ∃ i,
      (MonomialOrder.lex (σ := τ ⊕ₗ σ)).degree (b i) ≤
        (MonomialOrder.lex (σ := τ ⊕ₗ σ)).degree p) :
    ∃ r : (MvPolynomial (τ ⊕ₗ σ) R ⧸ J) →ₗ[R]
      (MvPolynomial σ R ⧸ J.comap (rename Sum.inrₗ).toRingHom),
        r.comp (eliminationQuotientMap J).toLinearMap = LinearMap.id := by
  classical
  let m : MonomialOrder σ := MonomialOrder.lex
  let n : MonomialOrder (τ ⊕ₗ σ) := MonomialOrder.lex
  let I : Ideal (MvPolynomial σ R) := J.comap (rename Sum.inrₗ).toRingHom
  let L : Set κ := {i | ∀ y, n.degree (b i) (Sum.inlₗ y) = 0}
  let a : L → MvPolynomial σ R := fun i => killCompl retained_injective (b i)
  have hren (i : L) : rename Sum.inrₗ (a i) = b i :=
    lex_rename_of_degree (b i) i.property
  have hdeg (i : L) : n.degree (b i) = (m.degree (a i)).mapDomain Sum.inrₗ := by
    rw [← hren i]
    exact lex_degree_rename (a i)
  have ha (i : L) : a i ∈ I := by
    change rename Sum.inrₗ (a i) ∈ J
    rw [hren]
    exact hb i
  have ham (i : L) : m.Monic (a i) := by
    have h := hm i
    change (b i).coeff (n.degree (b i)) = 1 at h
    rw [hdeg, ← hren i, coeff_rename_mapDomain _ retained_injective] at h
    exact h
  have eliminate (j : κ) (d : σ →₀ ℕ)
      (h : n.degree (b j) ≤ d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ)) :
      ∃ i : L, (i : κ) = j ∧ m.degree (a i) ≤ d := by
    have hz (y : τ) : n.degree (b j) (Sum.inlₗ y) = 0 := by
      have he := h (Sum.inlₗ y)
      have hd : d.mapDomain (Sum.inrₗ : σ → τ ⊕ₗ σ) (Sum.inlₗ y) = 0 := by
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨x, hx⟩
        cases hx
      rw [hd] at he
      exact Nat.eq_zero_of_le_zero he
    let i : L := ⟨j, hz⟩
    refine ⟨i, rfl, ?_⟩
    apply (Finsupp.mapDomain_le_mapDomain_iff_le retained_injective _ _).mp
    rw [← hdeg i]
    exact h
  have hai (p : MvPolynomial σ R) (hp : p ∈ I) (hn : p ≠ 0) :
      ∃ i, m.degree (a i) ≤ m.degree p := by
    have hpJ : rename (Sum.inrₗ : σ → τ ⊕ₗ σ) p ∈ J := hp
    have hp0 : rename (Sum.inrₗ : σ → τ ⊕ₗ σ) p ≠ 0 := by
      intro h
      exact hn ((rename_eq_zero_iff_of_injective p retained_injective).mp h)
    obtain ⟨j, hj⟩ := hi _ hpJ hp0
    rw [lex_degree_rename] at hj
    obtain ⟨i, _, hid⟩ := eliminate j (m.degree p) hj
    exact ⟨i, hid⟩
  have hs (d : σ →₀ ℕ) (hd : ∀ i, ¬ m.degree (a i) ≤ d)
      (j : κ) (hj : n.degree (b j) ≤ d.mapDomain Sum.inrₗ) : False := by
    obtain ⟨i, _, hid⟩ := eliminate j d hj
    exact hd i hid
  exact split_quotient_rename m n I J a b ha hb ham hm hai hi
    Sum.inrₗ retained_injective hs (eliminationQuotientMap J)
      (eliminationQuotientMap_mk J)

end FrobeniusSplitting
