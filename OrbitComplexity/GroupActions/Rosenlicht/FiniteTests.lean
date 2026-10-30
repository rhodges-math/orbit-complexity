import OrbitComplexity.GroupActions.Rosenlicht.OrbitIdeals
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite tests for bounded orbit relations

A family of linear equations on a finite-dimensional space is determined by a
finite subfamily. In particular, finitely many translates detect every polynomial
orbit relation up to a prescribed degree. Their evaluations form a finite matrix
for the bounded relation space.

## Main results

* `exists_finite_linear_tests`: finitely many members of a linear family detect its common kernel.
* `exists_finite_orbit_tests`: finitely many translates detect bounded-degree orbit relations.
-/

namespace GroupActions

noncomputable section

universe u v w z

variable {F : Type v} [Field F]

/-- A family of linear equations on a finite-dimensional space has the same common
kernel as a finite subfamily. -/
theorem exists_finite_linear_tests {V : Type w} [AddCommGroup V] [Module F V]
    [Module.Finite F V] {κ : Type z} (L : κ → Module.Dual F V) :
    ∃ s : Finset κ, ∀ v : V, (∀ i, L i v = 0) ↔ ∀ i ∈ s, L i v = 0 := by
  classical
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range L)).mp
      (IsNoetherian.noetherian (Submodule.span F (Set.range L)))
  have hidx : ∀ φ : t, ∃ i, L i = φ.val := fun φ ↦ ht φ.property
  let idx : t → κ := fun φ ↦ (hidx φ).choose
  let s : Finset κ := Finset.univ.image idx
  refine ⟨s, fun v ↦ ⟨fun h i _ ↦ h i, ?_⟩⟩
  intro hv i
  have htzero : ∀ φ ∈ t, φ v = 0 := by
    intro φ hφ
    let j : t := ⟨φ, hφ⟩
    have hj : idx j ∈ s := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hφ' := hv (idx j) hj
    rwa [(hidx j).choose_spec] at hφ'
  have hle : Submodule.span F (t : Set (Module.Dual F V)) ≤
      LinearMap.ker (Module.Dual.eval F V v) := by
    apply Submodule.span_le.mpr
    intro φ hφ
    exact htzero φ hφ
  exact hle (hspan ▸ Submodule.subset_span (Set.mem_range_self i))

variable {G : Type u} [Group G] [MulSemiringAction G F]
variable {ι : Type w} [Finite ι]

/-- Finitely many translates of a tuple test all its orbit relations up to a fixed
total degree. -/
theorem exists_finite_orbit_tests (x : ι → F) (d : ℕ) :
    ∃ s : Finset G, ∀ p : MvPolynomial ι F, p.totalDegree ≤ d →
      (p ∈ orbitIdeal (G := G) x ↔ ∀ g ∈ s, MvPolynomial.eval (fun i ↦ g • x i) p = 0) := by
  let V := MvPolynomial.restrictTotalDegree ι F d
  let L : G → Module.Dual F V := fun g ↦
    (MvPolynomial.aeval (fun i ↦ g • x i)).toLinearMap.comp V.subtype
  obtain ⟨s, hs⟩ := exists_finite_linear_tests L
  refine ⟨s, ?_⟩
  intro p hp
  rw [mem_orbitIdeal_iff]
  exact hs ⟨p, (MvPolynomial.mem_restrictTotalDegree ι d p).mpr hp⟩

end

end GroupActions
