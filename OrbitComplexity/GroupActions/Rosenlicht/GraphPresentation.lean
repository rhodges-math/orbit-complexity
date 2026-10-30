import OrbitComplexity.GroupActions.Rosenlicht.EliminationKernels
import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Sum.Order

/-!
# Polynomial presentations including prescribed coordinates

A finite-type algebra admits a polynomial presentation in which a given finite
tuple of coordinates occupies the final block of variables. The selected-variable
map to that quotient then recovers the given polynomial algebra map.
-/

open MvPolynomial

namespace GroupActions

noncomputable section

universe u v

/-- The second block of a lexicographic sum is identified with its image. -/
def rightVariableEquiv (n m : ℕ) :
    Fin m ≃ Set.range (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m) :=
  Equiv.ofInjective Sum.inrₗ (fun _ _ h ↦ Sum.inr.inj (congrArg ofLex h))

/-- A right-block variable has its original index under the range identification. -/
@[simp]
theorem rightVariableEquiv_val (n m : ℕ) (i : Fin m) :
    (rightVariableEquiv n m i).val = Sum.inrₗ i := rfl

/-- The second variable block is an upper set in the lexicographic sum order. -/
theorem rightVariables_isUpperSet (n m : ℕ) :
    IsUpperSet (Set.range (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m)) := by
  intro a b hab ha
  obtain ⟨i, rfl⟩ := ha
  rcases b with j | j
  · exact (Sum.Lex.not_inr_le_inl hab).elim
  · exact ⟨j, rfl⟩

/-- A polynomial map into a finite-type algebra is the final-coordinate map
of a polynomial quotient presentation, followed by an algebra isomorphism. -/
theorem exists_graph_presentation (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (m : ℕ) (f : MvPolynomial (Fin m) R →ₐ[R] A) :
    ∃ n : ℕ, ∃ I : Ideal (MvPolynomial (Fin n ⊕ₗ Fin m) R),
      ∃ e : (MvPolynomial (Fin n ⊕ₗ Fin m) R ⧸ I) ≃ₐ[R] A,
        e.toAlgHom.comp ((quotientVariableMap I
          (Set.range (Sum.inrₗ : Fin m → Fin n ⊕ₗ Fin m))).comp
            (MvPolynomial.rename (rightVariableEquiv n m))) = f := by
  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp
    inferInstance
  let z : Fin n ⊕ₗ Fin m → A :=
    fun i ↦ Sum.elim (fun j ↦ g (X j)) (fun j ↦ f (X j)) (ofLex i)
  let p : MvPolynomial (Fin n ⊕ₗ Fin m) R →ₐ[R] A := MvPolynomial.aeval z
  have hpg : p.comp (MvPolynomial.rename (Sum.inlₗ : Fin n → Fin n ⊕ₗ Fin m)) = g := by
    ext i
    simp [p, z]
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨q, rfl⟩ := hg a
    exact ⟨MvPolynomial.rename Sum.inlₗ q, AlgHom.congr_fun hpg q⟩
  let I := RingHom.ker p
  let e := Ideal.quotientKerAlgEquivOfSurjective hp
  refine ⟨n, I, e, ?_⟩
  ext i
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, quotientVariableMap_X]
  change e (Ideal.Quotient.mk I (X (rightVariableEquiv n m i).val)) = f (X i)
  rw [rightVariableEquiv_val, Ideal.quotientKerAlgEquivOfSurjective_mk]
  simp [p, z]

end

end GroupActions
