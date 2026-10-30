import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Radical Bracket Nilpotence

The bracket of a finite-dimensional Lie algebra with its solvable radical
acts nilpotently in every finite-dimensional representation. -/

noncomputable section
namespace ReductiveGroups

variable {K g V : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing g] [LieAlgebra K g] [Module.Finite K g]
  [AddCommGroup V] [Module K V] [LieRingModule g V] [LieModule K g V]
  [Module.Finite K V]

omit [IsAlgClosed K] [Module.Finite K g] in
private theorem bracket_trivial_on_radicalWeightSpace
    (A : LieIdeal K g) (χ : Module.Dual K A)
    (x : g) (y : A)
    (w : LieModule.weightSpaceOfIsLieTower (L := g) K V χ) :
    ⁅⁅x, (y : g)⁆, (w : V)⁆ = 0 := by
  let W : LieSubmodule K g V := LieModule.weightSpaceOfIsLieTower (L := g) K V χ
  have hw (z : A) : ⁅(z : g), (w : V)⁆ = χ z • (w : V) := by
    have hmem : (w : V) ∈ LieModule.weightSpace V χ := w.property
    exact (LieModule.mem_weightSpace χ (w : V)).mp hmem z
  have hxw : ⁅x, (w : V)⁆ ∈ W := W.lie_mem w.property
  have hyxw : ⁅(y : g), ⁅x, (w : V)⁆⁆ = χ y • ⁅x, (w : V)⁆ := by
    have hmem : ⁅x, (w : V)⁆ ∈ LieModule.weightSpace V χ := hxw
    exact (LieModule.mem_weightSpace χ ⁅x, (w : V)⁆).mp hmem y
  have h := leibniz_lie x (y : g) (w : V)
  rw [hw y, lie_smul, hyxw] at h
  exact add_right_cancel (show ⁅⁅x, (y : g)⁆, (w : V)⁆ + χ y • ⁅x, (w : V)⁆ =
    0 + χ y • ⁅x, (w : V)⁆ by simpa using h.symm)

omit [IsAlgClosed K] [Module.Finite K g] in
private theorem bracketIdeal_trivial_on_weightSpace
    (A : LieIdeal K g) (χ : Module.Dual K A) :
    ⁅(⊤ : LieIdeal K g), A⁆ ≤
      LieModule.ker K g (LieModule.weightSpaceOfIsLieTower (L := g) K V χ) := by
  rw [LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro z ⟨x, y, rfl⟩
  apply (LieModule.mem_ker K g _ _).mpr
  intro w
  apply Subtype.ext
  exact bracket_trivial_on_radicalWeightSpace (K := K) (V := V) A χ x y w

private theorem bracketIdeal_nilpotent_aux
    {K g : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [LieRing g] [LieAlgebra K g]
    (A : LieIdeal K g) [LieAlgebra.IsSolvable A] (n : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module K V]
      [LieRingModule g V] [LieModule K g V] [Module.Finite K V],
      Module.finrank K V ≤ n →
        LieModule.IsNilpotent (↥(⁅(⊤ : LieIdeal K g), A⁆ : LieIdeal K g)) V := by
  induction n with
  | zero =>
      intro V _ _ _ _ _ hn
      have hzero : Module.finrank K V = 0 := Nat.eq_zero_of_le_zero hn
      let _ : Subsingleton V := (Module.finrank_zero_iff).mp hzero
      infer_instance
  | succ n ih =>
      intro V _ _ _ _ _ hn
      by_cases hv : Subsingleton V
      · let _ : Subsingleton V := hv
        infer_instance
      let _ : Nontrivial V := not_subsingleton_iff_nontrivial.mp hv
      obtain ⟨χ, hχ⟩ :=
        LieModule.exists_nontrivial_weightSpace_of_isSolvable (k := K) (L := A) (V := V)
      let W : LieSubmodule K g V := LieModule.weightSpaceOfIsLieTower (L := g) K V χ
      let _ : Nontrivial W := hχ
      have hWpos : 0 < Module.finrank K W := Module.finrank_pos
      have hrank : Module.finrank K (V ⧸ W) ≤ n := by
        have hr := W.toSubmodule.finrank_quotient_add_finrank
        change Module.finrank K (V ⧸ W) + Module.finrank K W = Module.finrank K V at hr
        omega
      have hquot : LieModule.IsNilpotent (↥(⁅(⊤ : LieIdeal K g), A⁆ : LieIdeal K g)) (V ⧸ W) :=
        ih (V ⧸ W) hrank
      let H : LieIdeal K g := ⁅(⊤ : LieIdeal K g), A⁆
      let WH : LieSubmodule K H V :=
        { toSubmodule := W.toSubmodule
          lie_mem := fun {_ _} hm => W.lie_mem hm }
      have htriv : WH ≤ LieModule.maxTrivSubmodule K H V := by
        intro v hvw
        rw [LieModule.mem_maxTrivSubmodule]
        intro x
        have hx : (x : g) ∈ LieModule.ker K g W :=
          bracketIdeal_trivial_on_weightSpace (K := K) (V := V) A χ x.property
        have hx' := (LieModule.mem_ker K g W (x : g)).mp hx ⟨v, hvw⟩
        exact congrArg Subtype.val hx'
      exact LieModule.nilpotentOfNilpotentQuotient (R := K) (L := H) (M := V) htriv hquot

omit [Module.Finite K g] in
/-- The bracket of a Lie algebra with any solvable ideal acts nilpotently on a
finite-dimensional module over an algebraically closed field of characteristic zero. -/
theorem solvableIdeal_bracket_action_isNilpotent
    (A : LieIdeal K g) [LieAlgebra.IsSolvable A] :
    LieModule.IsNilpotent (↥(⁅(⊤ : LieIdeal K g), A⁆ : LieIdeal K g)) V :=
  bracketIdeal_nilpotent_aux A (Module.finrank K V) V le_rfl

/-- The full ideal `[g, radical(g)]` acts nilpotently in every finite-dimensional
representation of the original Lie algebra `g`. -/
theorem radicalBracket_action_isNilpotent :
    LieModule.IsNilpotent
      (↥(⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆ : LieIdeal K g)) V :=
  solvableIdeal_bracket_action_isNilpotent (K := K) (g := g) (V := V)
    (LieAlgebra.radical K g)

/-- Every element of `[g, radical(g)]` acts by a nilpotent endomorphism. -/
theorem radicalBracket_toEnd_isNilpotent {x : g}
    (hx : x ∈ (⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆ : LieIdeal K g)) :
    IsNilpotent (LieModule.toEnd K g V x) := by
  let H : LieIdeal K g := ⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆
  let _ : LieModule.IsNilpotent H V :=
    radicalBracket_action_isNilpotent (K := K) (g := g) (V := V)
  exact LieModule.isNilpotent_toEnd_of_isNilpotent K H V ⟨x, hx⟩

end ReductiveGroups
