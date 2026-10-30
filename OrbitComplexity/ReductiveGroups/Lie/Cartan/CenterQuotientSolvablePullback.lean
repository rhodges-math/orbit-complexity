import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalQuotient
import Mathlib.Algebra.Lie.Solvable

/-!
# Center Quotient Solvable Pullback

Solvability lifts through the quotient by the center: one extra
derived step kills the central kernel. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.Finite K L]

omit [CharZero K] [Module.Finite K L] in
/-- The inverse image of a solvable Lie subalgebra under the center
quotient is solvable. -/
theorem centerQuotient_comap_isSolvable
    (S : LieSubalgebra K (L ⧸ LieAlgebra.center K L))
    [IsSolvable S] :
    IsSolvable (S.comap (centerQuotientLieHom (K := K))) := by
  let P : LieSubalgebra K L := S.comap (centerQuotientLieHom (K := K))
  let qP : P →ₗ⁅K⁆ S := {
    toFun := fun p => ⟨centerQuotientLieHom (K := K) (p : L), p.property⟩
    map_add' := by intros; apply Subtype.ext; simp
    map_smul' := by intros; apply Subtype.ext; simp
    map_lie' := by intros; apply Subtype.ext; simp
  }
  have hqP : Function.Surjective qP := by
    intro s
    obtain ⟨x, hx⟩ := centerQuotientLieHom_surjective (K := K) (L := L) (s : _)
    have hmem : x ∈ P := by
      change centerQuotientLieHom (K := K) x ∈ S
      rw [hx]
      exact s.property
    exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩
  obtain ⟨k, hk⟩ := IsSolvable.solvable K S
  have hmap : (derivedSeries K P k).map qP = ⊥ := by
    rw [LieIdeal.derivedSeries_map_eq k hqP, hk]
  have hker : derivedSeries K P k ≤ qP.ker := by
    exact (LieIdeal.map_eq_bot_iff).mp hmap
  change IsSolvable P
  apply LieAlgebra.IsSolvable.mk (R := K) (L := P) (k := k + 1)
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ]
  apply (LieSubmodule.lie_eq_bot_iff
    (derivedSeries K P k) (derivedSeries K P k)).mpr
  intro a ha b hb
  have ha0' : qP a = 0 := hker ha
  have ha0 : centerQuotientLieHom (K := K) (a : L) = 0 :=
    congrArg Subtype.val ha0'
  have hcent : (a : L) ∈ LieAlgebra.center K L := by
    rw [← centerQuotientLieHom_ker]
    exact ha0
  have hbr' := (LieModule.mem_maxTrivSubmodule (R := K) (L := L) (M := L)
    (a : L)).mp hcent (b : L)
  have hbr : ⁅(a : L), (b : L)⁆ = 0 := by
    simpa only [hbr', neg_zero] using (lie_skew (a : L) (b : L)).symm
  exact Subtype.ext hbr

end ReductiveGroups
