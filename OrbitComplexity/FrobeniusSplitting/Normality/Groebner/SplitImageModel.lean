import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.MonicContraction
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.EliminationInclusion

/-! Coefficient models with split polynomial image inclusions. -/

open MvPolynomial

namespace FrobeniusSplitting

private theorem map_contraction_enlarge {σ K : Type*} [Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R) (I : Ideal (MvPolynomial σ K))
    (hI : (I.comap (map S.val.toRingHom)).map (map S.val.toRingHom) = I) :
    (I.comap (map R.val.toRingHom)).map (map R.val.toRingHom) = I := by
  let u : MvPolynomial σ S →+* MvPolynomial σ R :=
    map (Subalgebra.inclusion hSR).toRingHom
  let v : MvPolynomial σ R →+* MvPolynomial σ K := map R.val.toRingHom
  let w : MvPolynomial σ S →+* MvPolynomial σ K := map S.val.toRingHom
  have hcomp : v.comp u = w := by
    apply RingHom.ext
    intro p
    apply MvPolynomial.ext
    intro d
    simp only [RingHom.comp_apply, v, u, w, coeff_map]
    rfl
  have hle : (I.comap w).map u ≤ I.comap v := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change v (u p) ∈ I
    change (v.comp u) p ∈ I
    rw [hcomp]
    exact hp
  apply le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl)
  calc
    I = (I.comap w).map w := hI.symm
    _ = ((I.comap w).map u).map v := by rw [Ideal.map_map, hcomp]
    _ ≤ (I.comap v).map v := Ideal.map_mono hle

private theorem contraction_rename {σ τ K : Type*} [Field K]
    (R : Subalgebra ℤ K) (I : Ideal (MvPolynomial (τ ⊕ₗ σ) K)) :
    (I.comap (map R.val.toRingHom)).comap (rename Sum.inrₗ).toRingHom =
      (I.comap (rename (Sum.inrₗ : σ → τ ⊕ₗ σ)).toRingHom).comap
        (map R.val.toRingHom) := by
  ext p
  change map R.val.toRingHom (rename Sum.inrₗ p) ∈ I ↔
    rename Sum.inrₗ (map R.val.toRingHom p) ∈ I
  rw [map_rename]

/-- One coefficient model recovers both generic ideals and splits the image inclusion. -/
theorem exists_split_image_model {σ τ K : Type*} [LinearOrder σ] [LinearOrder τ]
    [Finite σ] [Finite τ] [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    (I : Ideal (MvPolynomial (τ ⊕ₗ σ) K)) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ _ : S ≤ R,
      let J := I.comap (map R.val.toRingHom)
      J.map (map R.val.toRingHom) = I ∧
      (J.comap (rename (Sum.inrₗ : σ → τ ⊕ₗ σ)).toRingHom).map
        (map R.val.toRingHom) = I.comap (rename Sum.inrₗ).toRingHom ∧
      Module.Free R (MvPolynomial (τ ⊕ₗ σ) R ⧸ J) ∧
      ∃ r : (MvPolynomial (τ ⊕ₗ σ) R ⧸ J) →ₗ[R]
        (MvPolynomial σ R ⧸ J.comap (rename Sum.inrₗ).toRingHom),
          r.comp (eliminationQuotientMap J).toLinearMap = LinearMap.id := by
  classical
  let A : Ideal (MvPolynomial σ K) :=
    I.comap (rename (Sum.inrₗ : σ → τ ⊕ₗ σ)).toRingHom
  obtain ⟨S', hS', hSS', _, _, _, _, _, _, _, hAS'⟩ :=
    exists_monic_contraction S hS MonomialOrder.lex A
  obtain ⟨R, hR, hS'R, t, b, hb, _, _, hi, _, hJR⟩ :=
    exists_monic_contraction S' hS' MonomialOrder.lex I
  let J : Ideal (MvPolynomial (τ ⊕ₗ σ) R) := I.comap (map R.val.toRingHom)
  let n : MonomialOrder (τ ⊕ₗ σ) := MonomialOrder.lex
  have hmem (i : t) : b i ∈ J := by
    change map R.val.toRingHom (b i) ∈ I
    rw [(hb i).1]
    exact (hb i).2.1
  have hmonic (i : t) : n.Monic (b i) := (hb i).2.2
  have hinit (p : MvPolynomial (τ ⊕ₗ σ) R) (hp : p ∈ J) (hn : p ≠ 0) :
      ∃ i, n.degree (b i) ≤ n.degree p := hi p hp hn
  have hsource : (J.comap (rename (Sum.inrₗ : σ → τ ⊕ₗ σ)).toRingHom).map
      (map R.val.toRingHom) = A := by
    change ((I.comap (map R.val.toRingHom)).comap (rename Sum.inrₗ).toRingHom).map
      (map R.val.toRingHom) = A
    rw [contraction_rename]
    exact map_contraction_enlarge S' R hS'R A hAS'
  have hfree : Module.Free R (MvPolynomial (τ ⊕ₗ σ) R ⧸ J) :=
    free_quotient_of_initial_monic n J b hmem hmonic hinit
  exact ⟨R, hR, hSS'.trans hS'R, hJR, hsource, hfree,
    split_elimination_quotient J b hmem hmonic hinit⟩

end FrobeniusSplitting
