import OrbitComplexity.ReductiveGroups.Lie.Exponential.AssociativeRadicalNilpotence

/-!
# Associative Radical Word Bound

A uniform bound on mixed products from the radical bracket, independent of
the chosen factors. -/

noncomputable section
namespace ReductiveGroups
open LieModule

variable {K g A : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing g] [LieAlgebra K g] [Module.Finite K g]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

attribute [local instance] LieRing.ofAssociativeRing

omit [CharZero K] [IsAlgClosed K] in
private theorem lieWord_mem_lowerCentralSeries
    {H M : Type*} [LieRing H] [LieAlgebra K H]
    [AddCommGroup M] [Module K M] [LieRingModule H M]
    (xs : List H) (m : M) :
    xs.foldr (fun (x : H) (v : M) => ⁅x, v⁆) m ∈
      LieModule.lowerCentralSeries K H M xs.length := by
  induction xs with
  | nil => simp only [List.foldr_nil, List.length_nil, LieModule.lowerCentralSeries_zero,
      LieSubmodule.mem_top]
  | cons x xs ih =>
      simpa only [List.foldr_cons, List.length_cons, LieModule.lowerCentralSeries_succ] using
        (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih)

/-- In every finite-dimensional associative representation, sufficiently long
mixed words of elements of the `[g, radical(g)]` vanish. The bound is
uniform over all choices and orders of factors. -/
theorem AssociativeRadicalWordBound.exists_associative_word_bound
    (f : g →ₗ⁅K⁆ A) :
    ∃ N : ℕ, ∀ xs : List
      (↥(⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆ : LieIdeal K g)),
      xs.length = N → (xs.map (fun (x : ↥(⁅(⊤ : LieIdeal K g),
        LieAlgebra.radical K g⁆ : LieIdeal K g)) => f (x : g))).prod = 0 := by
  let H : LieIdeal K g := ⁅(⊤ : LieIdeal K g), LieAlgebra.radical K g⁆
  let : LieRingModule A (ULift.{0} A) := LieRingModule.ofAssociativeModule
  let : LieModule K A (ULift.{0} A) := LieModule.ofAssociativeModule
  let : LieRingModule g (ULift.{0} A) := LieRingModule.compLieHom (ULift.{0} A) f
  let : LieModule K g (ULift.{0} A) := LieModule.compLieHom (ULift.{0} A) f
  let : LieModule.IsNilpotent H (ULift.{0} A) :=
    radicalBracket_action_isNilpotent (K := K) (g := g) (V := ULift.{0} A)
  obtain ⟨N, hN⟩ := LieModule.IsNilpotent.nilpotent K H (ULift.{0} A)
  refine ⟨N, ?_⟩
  intro xs hlen
  have hact (ys : List H) (a : A) :
      ys.foldr (fun (x : H) (v : ULift.{0} A) => ⁅x, v⁆) (ULift.up a) =
        ULift.up ((ys.map (fun (x : H) => f (x : g))).prod * a) := by
    induction ys with
    | nil => simp
    | cons x ys ih =>
        simp only [List.foldr_cons, List.map_cons, List.prod_cons]
        rw [ih]
        change ULift.up (f (x : g) * ((ys.map (fun (z : H) => f (z : g))).prod * a)) = _
        simp only [mul_assoc]
  have hzero : xs.foldr (fun (x : H) (v : ULift.{0} A) => ⁅x, v⁆)
      (ULift.up (1 : A)) = 0 := by
    have hm := lieWord_mem_lowerCentralSeries (K := K) xs (ULift.up (1 : A))
    rw [hlen, hN] at hm
    simpa only [LieSubmodule.mem_bot] using hm
  have hzero' := congrArg ULift.down hzero
  rw [hact xs (1 : A)] at hzero'
  simpa using hzero'

end ReductiveGroups
