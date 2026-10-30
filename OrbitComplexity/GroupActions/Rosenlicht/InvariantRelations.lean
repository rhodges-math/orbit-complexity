import OrbitComplexity.GroupActions.Rosenlicht.CoefficientCharts
import OrbitComplexity.GroupActions.Rosenlicht.OrbitIdeals

/-!
# Invariant coefficients of orbit relations

Normalizing a bounded relation space by coordinate entries gives a basis whose
coefficients are fixed by the group. A sufficiently large relation space generates
the entire orbit ideal, so finitely many polynomials with invariant coefficients
generate that ideal.

## Main results

* `exists_fixed_orbitRelation_basis`: a bounded relation space has a basis with fixed coefficients.
* `exists_fixed_orbitIdeal_generators`: finitely many such polynomials generate the orbit ideal.
-/

namespace GroupActions

noncomputable section

universe u v w

variable {G : Type u} [Group G] {F : Type v} [Field F]
variable [MulSemiringAction G F] {ι : Type w} [Finite ι]

/-- A bounded-degree orbit relation space has a finite basis of polynomials with
group-invariant coefficients. -/
theorem exists_fixed_orbitRelation_basis (x : ι → F) (d : ℕ) :
    ∃ (s : Set (Module.Dual F (orbitRelations (G := G) x d))) (_ : s.Finite)
      (b : Module.Basis s F (orbitRelations (G := G) x d)),
      ∀ (g : G) (j : s) (m : ι →₀ ℕ), g • (b j).val.coeff m = (b j).val.coeff m := by
  classical
  let W := orbitRelations (G := G) x d
  let L : (ι →₀ ℕ) → Module.Dual F W := fun m ↦
    (MvPolynomial.lcoeff F m).comp W.subtype
  have hL : ∀ z : W, z ≠ 0 → ∃ m, L m z ≠ 0 := by
    intro z hz
    by_contra! h
    apply hz
    apply Subtype.ext
    apply MvPolynomial.ext
    exact h
  obtain ⟨s, hs, c, e, he⟩ := exists_linearCoordinateChart L hL
  let _ := hs.fintype
  let b : Module.Basis s F W := (Pi.basisFun F s).map e.symm
  have hb (j k : s) : (b j).val.coeff (c k) = if k = j then 1 else 0 := by
    change L (c k) (b j) = _
    rw [← he]
    simp [b, Pi.basisFun_apply, Pi.single_apply]
  refine ⟨s, hs, b, ?_⟩
  intro g j m
  let q := MvPolynomial.map (MulSemiringAction.toRingHom G F g) (b j).val
  have hq : q ∈ W :=
    (orbitRelations_map_mem_iff x d (b j).val g).mpr (b j).property
  have h : e ⟨q, hq⟩ = e (b j) := by
    funext k
    rw [he, he]
    change q.coeff (c k) = (b j).val.coeff (c k)
    rw [MvPolynomial.coeff_map]
    change g • (b j).val.coeff (c k) = (b j).val.coeff (c k)
    rw [hb]
    split_ifs <;> simp only [smul_one, smul_zero]
  have hpoly : q = (b j).val := congrArg Subtype.val (e.injective h)
  simpa only [q, MvPolynomial.coeff_map, MulSemiringAction.toRingHom_apply]
    using congrArg (fun p : MvPolynomial ι F ↦ p.coeff m) hpoly

/-- Finitely many orbit relations with group-invariant coefficients generate the
whole orbit ideal. -/
theorem exists_fixed_orbitIdeal_generators (x : ι → F) :
    ∃ s : Finset (MvPolynomial ι F), Ideal.span (s : Set (MvPolynomial ι F)) =
      orbitIdeal (G := G) x ∧
      ∀ p ∈ s, ∀ (g : G) (m : ι →₀ ℕ), g • p.coeff m = p.coeff m := by
  classical
  obtain ⟨d, hd⟩ := exists_orbitRelation_degree (G := G) x
  obtain ⟨s, hs, b, hb⟩ := exists_fixed_orbitRelation_basis (G := G) x d
  let _ := hs.fintype
  let t : Finset (MvPolynomial ι F) := Finset.univ.image fun j ↦ (b j).val
  have ht : (t : Set (MvPolynomial ι F)) = Set.range fun j ↦ (b j).val := by
    simp [t]
  refine ⟨t, ?_, ?_⟩
  · rw [ht, ← hd]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro p ⟨j, rfl⟩
      exact (b j).property
    · apply Ideal.span_le.mpr
      intro p hp
      let J := Ideal.span (Set.range fun j ↦ (b j).val)
      have hle : (⊤ : Submodule F (orbitRelations (G := G) x d)) ≤
          (J.restrictScalars F).comap (orbitRelations (G := G) x d).subtype := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro z ⟨j, rfl⟩
        exact Ideal.subset_span (Set.mem_range_self j)
      exact hle (Submodule.mem_top (x := ⟨p, hp⟩))
  · intro p hp g m
    change p ∈ (t : Set (MvPolynomial ι F)) at hp
    rw [ht] at hp
    obtain ⟨j, rfl⟩ := hp
    exact hb g j m

end

end GroupActions
