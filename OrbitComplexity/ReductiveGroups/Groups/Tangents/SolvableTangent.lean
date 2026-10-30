import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWordIdentity
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWordInfinitesimal
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedWordSolvability
import OrbitComplexity.ReductiveGroups.Groups.Tangents.InfinitesimalTangentDetection

/-!
# Solvable Tangent

Solvability of rational points implies solvability of the
tangent Lie algebra of a reduced affine group of finite type. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [IsReduced B]

/-- Differentiate a balanced group identity using independent leaf
parameters and extract its full mixed coefficient. -/
theorem DerivedLieWord.eq_zero_of_rational_word_identity
    (n : ℕ)
    (h : ∀ x : DerivedWordIndex n → WithConv (B →ₐ[K] K),
      derivedGroupWord n x = 1)
    (d : DerivedWordIndex n → Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    derivedLieWord n d = 0 := by
  apply InfinitesimalTangentDetection.eq_zero_of_fullParameter_point_eq_one n
  rw [← derivedInfinitesimalGroupWord_eq_tangent]
  exact derivedGroupWord_eq_one_of_rational n h _

/-- The tangent derived series terminates at any depth where the
original rational-point derived series terminates. -/
theorem SolvableTangent.eq_bot_of_point_derivedSeries_eq_bot
    (n : ℕ) (h : derivedSeries (WithConv (B →ₐ[K] K)) n = ⊥) :
    LieAlgebra.derivedSeries K
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) n = ⊥ := by
  apply DerivedSeries.eq_bot_of_derivedLieWord_eq_zero (R := K) n
  exact DerivedLieWord.eq_zero_of_rational_word_identity n
    (fun x => DerivedGroupWord.eq_one_of_derivedSeries_eq_bot n h x)

/-- The tangent Lie algebra of a reduced finite-type affine group
with solvable rational points is solvable. -/
theorem SolvableTangent.isSolvable_of_rational_points_isSolvable
    [Group.IsSolvable (WithConv (B →ₐ[K] K))] :
    LieAlgebra.IsSolvable
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) := by
  obtain ⟨n, hn⟩ :=
    DerivedWordSolvability.exists_identity_of_isSolvable (G := WithConv (B →ₐ[K] K))
  exact lie_isSolvable_of_derivedLieWord_eq_zero n
    (DerivedLieWord.eq_zero_of_rational_word_identity n hn)

end ReductiveGroups
