import Mathlib.Algebra.Ring.Action.Group
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial relations of an orbit

The relations of a tuple in a field are tested at every translate of the tuple.
Applying a group element to the coefficients preserves these relations. The
bounded-degree relation spaces therefore carry the same coefficient action.

## Main definitions

* `orbitIdeal`: the ideal vanishing on every translate of a tuple.
* `orbitRelations`: the vector space of orbit relations of bounded total degree.

## Main results

* `orbitIdeal_map_mem_iff`: coefficient automorphisms preserve orbit relations.
* `orbitRelations_map_mem_iff`: the same statement with a degree bound.
* `exists_orbitRelation_degree`: one bounded-degree relation space generates the ideal.
-/

namespace GroupActions

noncomputable section

universe u v w

variable {G : Type u} [Group G] {F : Type v} [Field F]
variable [MulSemiringAction G F] {ι : Type w}

/-- The ideal of polynomial relations satisfied by every translate of a tuple. -/
def orbitIdeal (x : ι → F) : Ideal (MvPolynomial ι F) :=
  MvPolynomial.vanishingIdeal F (Set.range fun g : G ↦ fun i ↦ g • x i)

/-- A polynomial is an orbit relation exactly when it vanishes at every translate. -/
theorem mem_orbitIdeal_iff (x : ι → F) (p : MvPolynomial ι F) :
    p ∈ orbitIdeal (G := G) x ↔ ∀ g : G, MvPolynomial.eval (fun i ↦ g • x i) p = 0 := by
  simp [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff,
    MvPolynomial.aeval_eq_eval]

private lemma eval_map_translate (x : ι → F) (p : MvPolynomial ι F) (g h : G) :
    MvPolynomial.eval (fun i ↦ h • x i)
      (MvPolynomial.map (MulSemiringAction.toRingHom G F g) p) =
        g • MvPolynomial.eval (fun i ↦ (g⁻¹ * h) • x i) p := by
  change _ = MulSemiringAction.toRingHom G F g
    (MvPolynomial.eval (fun i ↦ (g⁻¹ * h) • x i) p)
  rw [MvPolynomial.map_eval]
  congr 2
  funext i
  simp only [Function.comp_apply, MulSemiringAction.toRingHom_apply, ← mul_smul,
    mul_inv_cancel_left]

/-- Applying a group element to the coefficients preserves the orbit ideal. -/
theorem orbitIdeal_map_mem_iff (x : ι → F) (p : MvPolynomial ι F) (g : G) :
    MvPolynomial.map (MulSemiringAction.toRingHom G F g) p ∈ orbitIdeal (G := G) x ↔
      p ∈ orbitIdeal (G := G) x := by
  simp only [mem_orbitIdeal_iff, eval_map_translate]
  constructor
  · intro hp h
    have := hp (g * h)
    simpa only [inv_mul_cancel_left, smul_eq_zero_iff_eq] using this
  · intro hp h
    rw [hp, smul_zero]

/-- The vector space of orbit relations with bounded total degree. -/
def orbitRelations (x : ι → F) (d : ℕ) : Submodule F (MvPolynomial ι F) :=
  (orbitIdeal (G := G) x).restrictScalars F ⊓ MvPolynomial.restrictTotalDegree ι F d

/-- Membership in a bounded relation space records both vanishing and the degree bound. -/
theorem mem_orbitRelations_iff (x : ι → F) (d : ℕ) (p : MvPolynomial ι F) :
    p ∈ orbitRelations (G := G) x d ↔
      p ∈ orbitIdeal (G := G) x ∧ p.totalDegree ≤ d := by
  simp [orbitRelations, MvPolynomial.mem_restrictTotalDegree]

private lemma totalDegree_map_action (p : MvPolynomial ι F) (g : G) :
    (MvPolynomial.map (MulSemiringAction.toRingHom G F g) p).totalDegree =
      p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  congr 1
  exact MvPolynomial.support_map_of_injective _ (MulSemiringAction.toRingEquiv G F g).injective

/-- Coefficient automorphisms preserve each bounded-degree relation space. -/
theorem orbitRelations_map_mem_iff (x : ι → F) (d : ℕ) (p : MvPolynomial ι F) (g : G) :
    MvPolynomial.map (MulSemiringAction.toRingHom G F g) p ∈
      orbitRelations (G := G) x d ↔ p ∈ orbitRelations (G := G) x d := by
  simp only [mem_orbitRelations_iff, orbitIdeal_map_mem_iff, totalDegree_map_action]

/-- For finitely many variables, each bounded-degree orbit relation space is finite
dimensional. -/
instance [Finite ι] (x : ι → F) (d : ℕ) :
    Module.Finite F (orbitRelations (G := G) x d) :=
  Module.Finite.of_injective
    (Submodule.inclusion
      (show orbitRelations (G := G) x d ≤ MvPolynomial.restrictTotalDegree ι F d from
        inf_le_right))
    (Submodule.inclusion_injective _)

/-- Finitely many variables admit a degree bound whose relation space generates
the whole orbit ideal. -/
theorem exists_orbitRelation_degree [Finite ι] (x : ι → F) :
    ∃ d, Ideal.span (orbitRelations (G := G) x d : Set (MvPolynomial ι F)) =
      orbitIdeal (G := G) x := by
  classical
  obtain ⟨s, hs⟩ := (orbitIdeal (G := G) x).fg_of_isNoetherianRing
  refine ⟨s.sup MvPolynomial.totalDegree, le_antisymm ?_ ?_⟩
  · exact Ideal.span_le.mpr fun p hp ↦ (mem_orbitRelations_iff x _ p).mp hp |>.1
  · rw [← hs]
    apply Ideal.span_mono
    intro p hp
    exact (mem_orbitRelations_iff x _ p).mpr
      ⟨hs ▸ Ideal.subset_span hp, Finset.le_sup hp⟩

end

end GroupActions
