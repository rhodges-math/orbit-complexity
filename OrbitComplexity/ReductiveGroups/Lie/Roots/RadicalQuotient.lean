import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Quotient

/-!
# Radical Quotient

The quotient of a finite-dimensional Lie algebra by its solvable radical
has trivial radical.  -/

noncomputable section
namespace ReductiveGroups

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

private def quotientLieHom (I : LieIdeal K L) : L →ₗ⁅K⁆ (L ⧸ I) where
  toLinearMap := (LieSubmodule.Quotient.mk' I).toLinearMap
  map_lie' := by intros; rfl

private theorem solvable_of_derived_le_solvable
    {I J : LieIdeal K L} [LieAlgebra.IsSolvable J]
    (m : ℕ) (h : LieAlgebra.derivedSeriesOfIdeal K L m I ≤ J) :
    LieAlgebra.IsSolvable I := by
  obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable K J
  have hj : LieAlgebra.derivedSeriesOfIdeal K L n J = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff J n).mp hn
  apply LieAlgebra.IsSolvable.mk (R := K) (L := I) (k := n + m)
  apply (LieIdeal.derivedSeries_eq_bot_iff I (n + m)).mpr
  rw [LieAlgebra.derivedSeriesOfIdeal_add]
  exact bot_unique ((LieAlgebra.derivedSeriesOfIdeal_mono h n).trans (le_of_eq hj))

/-- The solvable radical has a semisimple quotient in the precise sense of
trivial quotient radical. -/
theorem hasTrivialRadical_quotient_radical [Module.Finite K L] :
    LieAlgebra.HasTrivialRadical K (L ⧸ LieAlgebra.radical K L) := by
  let R := LieAlgebra.radical K L
  let q : L →ₗ⁅K⁆ (L ⧸ R) := quotientLieHom R
  apply LieAlgebra.hasTrivialRadical_of_no_solvable_ideals
  intro J hJ
  let P : LieIdeal K L := J.comap q
  have hP : ∀ m : ℕ,
      LieAlgebra.derivedSeriesOfIdeal K L m P ≤
        (LieAlgebra.derivedSeriesOfIdeal K (L ⧸ R) m J).comap q := by
    intro m
    induction m with
    | zero => exact le_refl _
    | succ m ih =>
      rw [show m + 1 = Nat.succ m from rfl]
      simp only [LieAlgebra.derivedSeriesOfIdeal_succ]
      exact (LieSubmodule.mono_lie ih ih).trans (LieIdeal.comap_bracket_le q)
  obtain ⟨m, hm⟩ := LieAlgebra.IsSolvable.solvable K J
  have hj : LieAlgebra.derivedSeriesOfIdeal K (L ⧸ R) m J = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff J m).mp hm
  have hPR : LieAlgebra.derivedSeriesOfIdeal K L m P ≤ R := by
    calc
      LieAlgebra.derivedSeriesOfIdeal K L m P ≤
          (LieAlgebra.derivedSeriesOfIdeal K (L ⧸ R) m J).comap q := hP m
      _ = q.ker := by rw [hj]; rfl
      _ = R := by
        ext x
        change (LieSubmodule.Quotient.mk' R x = 0) ↔ x ∈ R
        exact LieSubmodule.Quotient.mk_eq_zero (N := R) (m := x)
  have hsolv : LieAlgebra.IsSolvable P :=
    solvable_of_derived_le_solvable m hPR
  have hle : P ≤ R :=
    (LieAlgebra.LieIdeal.solvable_iff_le_radical (R := K) (L := L) P).mp hsolv
  have hJ : J = ⊥ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := (LieSubmodule.Quotient.surjective_mk' R) x
      have hy : y ∈ P := hx
      have hyr : y ∈ R := hle hy
      exact by simpa [q, quotientLieHom] using hyr
    · exact bot_le
  exact hJ

end ReductiveGroups
