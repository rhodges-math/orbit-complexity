import OrbitComplexity.GroupActions.Rosenlicht.DivisionSupport

/-!
# Complemented coordinate images in polynomial quotients

For a downward closed monomial set, division preserves its support constraint.
In the standard-monomial basis of a quotient, its image is therefore a
coordinate subspace and has the complementary standard monomials as a complement.
-/

open MvPolynomial
open scoped MonomialOrder

namespace GroupActions

noncomputable section

universe u v

variable {σ : Type u} {R : Type v} [CommRing R]

/-- The image in a polynomial quotient of the submodule supported on a given
set of monomials. -/
def quotientSupport (I : Ideal (MvPolynomial σ R)) (t : Set (σ →₀ ℕ)) :
    Submodule R (MvPolynomial σ R ⧸ I) :=
  (restrictSupport R t).map (I.restrictScalars R).mkQ

/-- In a quotient with a leading-monomial basis, a downward closed monomial
subspace is complemented by the remaining standard monomials. -/
theorem isCompl_quotientSupport (m : MonomialOrder σ)
    (s : Finset (MvPolynomial σ R)) (hu : ∀ q ∈ s, IsUnit (m.leadingCoeff q))
    (hd : ∀ p ∈ Ideal.span (s : Set (MvPolynomial σ R)), p ≠ 0 →
      ∃ q ∈ s, m.degree q ≤ m.degree p)
    (t : Set (σ →₀ ℕ)) (ht : ∀ a b, a ≼[m] b → b ∈ t → a ∈ t) :
    IsCompl (quotientSupport (Ideal.span (s : Set (MvPolynomial σ R))) t)
      (quotientSupport (Ideal.span (s : Set (MvPolynomial σ R)))
        (standardMonomials m s \ t)) := by
  classical
  let I := Ideal.span (s : Set (MvPolynomial σ R))
  let J := I.restrictScalars R
  let q := J.mkQ
  let N := normalForms m s
  let U := restrictSupport R t
  let W := restrictSupport R (standardMonomials m s \ t)
  have hc : IsCompl J N := isCompl_normalForms m I s
    (fun _ hp ↦ Ideal.subset_span hp) hu hd
  have hW : W ≤ N := restrictSupport_mono _ Set.sdiff_subset
  have hUW : Disjoint U W := by
    apply Submodule.disjoint_def.mpr
    intro p hpU hpW
    apply MvPolynomial.ext
    intro d
    change p.coeff d = 0
    by_contra h
    have hd' : d ∈ p.support := MvPolynomial.mem_support_iff.mpr h
    exact (hpW hd').2 (hpU hd')
  change IsCompl (U.map q) (W.map q)
  constructor
  · apply Submodule.disjoint_def.mpr
    intro z hzU hzW
    obtain ⟨p, hp, hpz⟩ := Submodule.mem_map.mp hzU
    obtain ⟨c, hcW, hcz⟩ := Submodule.mem_map.mp hzW
    obtain ⟨r, hrN, hrT, hpr⟩ := exists_supported_normalForm m s hu t ht p hp
    have hqr : q p = q r := (Submodule.Quotient.eq J).mpr hpr
    have hrc : r - c ∈ J := (Submodule.Quotient.eq J).mp
      (hqr.symm.trans (hpz.trans hcz.symm))
    have he : r = c := sub_eq_zero.mp
      (hc.disjoint.le_bot ⟨hrc, N.sub_mem hrN (hW hcW)⟩)
    have hc0 : c = 0 := (Submodule.disjoint_def.mp hUW) c (he ▸ hrT) hcW
    calc
      z = q c := hcz.symm
      _ = 0 := by rw [hc0, map_zero]
  · have hsplit : N = restrictSupport R (standardMonomials m s ∩ t) ⊔ W := by
      have he : (standardMonomials m s ∩ t) ∪ (standardMonomials m s \ t) =
          standardMonomials m s := by
        ext d
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
        tauto
      change AddMonoidAlgebra.supported R R (standardMonomials m s) =
        AddMonoidAlgebra.supported R R (standardMonomials m s ∩ t) ⊔
          AddMonoidAlgebra.supported R R (standardMonomials m s \ t)
      simp only [AddMonoidAlgebra.supported_eq_map, ← Submodule.map_sup,
        ← Finsupp.supported_union, he]
    have hle : N ≤ U ⊔ W := by
      rw [hsplit]
      exact sup_le ((restrictSupport_mono R Set.inter_subset_right).trans le_sup_left)
        le_sup_right
    have hm : N.map q = ⊤ := (Submodule.map_mkQ_eq_top J N).mpr hc.sup_eq_top
    rw [codisjoint_iff]
    apply top_unique
    have h := Submodule.map_mono (f := q) hle
    rwa [Submodule.map_sup, hm] at h

end

end GroupActions
