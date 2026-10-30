import Mathlib.Algebra.Lie.Solvable

/-!
# Radical Characteristic

The solvable radical and its bracket with the ambient Lie algebra are
characteristic ideals. -/

noncomputable section
namespace ReductiveGroups

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [IsNoetherian K L]

/-- A Lie automorphism preserves the solvable radical. -/
theorem radical_map_lieEquiv (e : L ≃ₗ⁅K⁆ L) :
    (LieAlgebra.radical K L).map e.toLieHom = LieAlgebra.radical K L := by
  let R := LieAlgebra.radical K L
  have hmap (n : ℕ) :
      LieAlgebra.derivedSeriesOfIdeal K L n (R.map e.toLieHom) =
        (LieAlgebra.derivedSeriesOfIdeal K L n R).map e.toLieHom := by
    induction n with
    | zero => simp [LieAlgebra.derivedSeriesOfIdeal_zero]
    | succ n ih =>
        rw [LieAlgebra.derivedSeriesOfIdeal_succ,
          LieAlgebra.derivedSeriesOfIdeal_succ, ih,
          LieIdeal.map_bracket_eq e.toLieHom e.surjective]
  have hsolv : LieAlgebra.IsSolvable (R.map e.toLieHom) := by
    obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable K R
    have hnil : LieAlgebra.derivedSeries K (R.map e.toLieHom) n = ⊥ := by
      rw [LieIdeal.derivedSeries_eq_bot_iff] at hn ⊢
      rw [hmap, hn]
      simp
    exact LieAlgebra.IsSolvable.mk hnil
  have hle : R.map e.toLieHom ≤ R :=
    le_sSup hsolv
  have hle' : R.map e.symm.toLieHom ≤ R := by
    let f := e.symm
    have hmap' (n : ℕ) :
        LieAlgebra.derivedSeriesOfIdeal K L n (R.map f.toLieHom) =
          (LieAlgebra.derivedSeriesOfIdeal K L n R).map f.toLieHom := by
      induction n with
      | zero => simp [LieAlgebra.derivedSeriesOfIdeal_zero]
      | succ n ih =>
          rw [LieAlgebra.derivedSeriesOfIdeal_succ,
            LieAlgebra.derivedSeriesOfIdeal_succ, ih,
            LieIdeal.map_bracket_eq f.toLieHom f.surjective]
    have hs : LieAlgebra.IsSolvable (R.map f.toLieHom) := by
      obtain ⟨n, hn⟩ := LieAlgebra.IsSolvable.solvable K R
      have hnil : LieAlgebra.derivedSeries K (R.map f.toLieHom) n = ⊥ := by
        rw [LieIdeal.derivedSeries_eq_bot_iff] at hn ⊢
        rw [hmap', hn]
        simp
      exact LieAlgebra.IsSolvable.mk hnil
    exact le_sSup hs
  apply le_antisymm hle
  intro x hx
  have h₁ := LieIdeal.mem_map (f := e.symm.toLieHom) hx
  have h₂ := hle' h₁
  have h₃ := LieIdeal.mem_map (f := e.toLieHom) h₂
  simpa using h₃

/-- The derived radical `[L, radical L]` is characteristic. -/
theorem bracket_radical_map_lieEquiv (e : L ≃ₗ⁅K⁆ L) :
    (⁅(⊤ : LieIdeal K L), LieAlgebra.radical K L⁆).map e.toLieHom =
      ⁅(⊤ : LieIdeal K L), LieAlgebra.radical K L⁆ := by
  rw [LieIdeal.map_bracket_eq e.toLieHom e.surjective]
  rw [radical_map_lieEquiv e]
  have htop : (⊤ : LieIdeal K L).map e.toLieHom = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    simpa using (LieIdeal.mem_map (f := e.toLieHom)
      (I := (⊤ : LieIdeal K L)) (LieSubmodule.mem_top (e.symm x)))
  rw [htop]

end ReductiveGroups
