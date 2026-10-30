import OrbitComplexity.ReductiveGroups.Groups.TangentOperators.SquareZeroPointCommutator
import OrbitComplexity.ReductiveGroups.Groups.Representations.InfinitesimalWordParameters
import OrbitComplexity.ReductiveGroups.Lie.Roots.DerivedLieWords

/-!
# Derived Group Word Infinitesimal

Balanced derived words of infinitesimal affine-group points
are exactly the tangent points of the corresponding derived Lie words. -/

noncomputable section
namespace ReductiveGroups

open WithConv
open scoped TensorProduct commutatorElement

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

private abbrev C := TauCeti.Bialgebra.CounitAlgebra K B K

private def leftParameterMap (n : ℕ) :
    InfinitesimalWordParameters K n →ₐ[K] InfinitesimalWordParameters K (n + 1) :=
  Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (A := InfinitesimalWordParameters K n) (B := InfinitesimalWordParameters K n)

private def rightParameterMap (n : ℕ) :
    InfinitesimalWordParameters K n →ₐ[K] InfinitesimalWordParameters K (n + 1) :=
  Algebra.TensorProduct.includeRight (R := K)
    (A := InfinitesimalWordParameters K n) (B := InfinitesimalWordParameters K n)

private theorem leftParameterMap_leaf (n : ℕ) (i : DerivedWordIndex n) :
    leftParameterMap (K := K) n (infinitesimalWordLeaf K n i) =
      infinitesimalWordLeaf K (n + 1) (false, i) := rfl

private theorem rightParameterMap_leaf (n : ℕ) (i : DerivedWordIndex n) :
    rightParameterMap (K := K) n (infinitesimalWordLeaf K n i) =
      infinitesimalWordLeaf K (n + 1) (true, i) := rfl

private theorem parameterMap_mul (n : ℕ) :
    leftParameterMap (K := K) n (infinitesimalWordParameter K n) *
      rightParameterMap (K := K) n (infinitesimalWordParameter K n) =
        infinitesimalWordParameter K (n + 1) := by
  exact infinitesimalWordParameter_split (K := K) n

/-- The balanced derived commutator word of depth `n` evaluated on the infinitesimal points
`squareZeroTangentPoint (d i)` at independent square-zero leaf parameters, with values in
`InfinitesimalWordParameters K n`. -/
def derivedInfinitesimalGroupWord (n : ℕ)
    (d : DerivedWordIndex n → Derivation K B (C (K := K) (B := B))) :
    WithConv (B →ₐ[K] InfinitesimalWordParameters K n) :=
  derivedGroupWord n (fun i => squareZeroTangentPoint (d i)
    (infinitesimalWordLeaf K n i) (infinitesimalWordLeaf_sq_zero K n i))

private theorem leftBranch_word (n : ℕ)
    (d : DerivedWordIndex (n + 1) → Derivation K B (C (K := K) (B := B))) :
    derivedGroupWord n (fun i => squareZeroTangentPoint (d (false, i))
      (infinitesimalWordLeaf K (n + 1) (false, i))
      (infinitesimalWordLeaf_sq_zero K (n + 1) (false, i))) =
    TauCeti.AlgHom.mapValue (leftParameterMap (K := K) n)
      (derivedInfinitesimalGroupWord n (fun i => d (false, i))) := by
  change (Bool × DerivedWordIndex n → Derivation K B (C (K := K) (B := B))) at d
  calc
    _ = derivedGroupWord n (fun i =>
        TauCeti.AlgHom.mapValue (leftParameterMap (K := K) n)
          (squareZeroTangentPoint (d (false, i))
            (infinitesimalWordLeaf K n i)
            (infinitesimalWordLeaf_sq_zero K n i))) := by
          congr 1
          funext i
          simpa only [leftParameterMap_leaf] using
            (squareZeroTangentPoint_map (d (false, i))
              (leftParameterMap (K := K) n)
              (infinitesimalWordLeaf K n i)
              (infinitesimalWordLeaf_sq_zero K n i)).symm
    _ = _ := by
      simpa only [derivedInfinitesimalGroupWord] using
        (derivedGroupWord_map
          (TauCeti.AlgHom.mapValue (leftParameterMap (K := K) n)) n
          (fun i => squareZeroTangentPoint (d (false, i))
            (infinitesimalWordLeaf K n i)
            (infinitesimalWordLeaf_sq_zero K n i))).symm

private theorem rightBranch_word (n : ℕ)
    (d : DerivedWordIndex (n + 1) → Derivation K B (C (K := K) (B := B))) :
    derivedGroupWord n (fun i => squareZeroTangentPoint (d (true, i))
      (infinitesimalWordLeaf K (n + 1) (true, i))
      (infinitesimalWordLeaf_sq_zero K (n + 1) (true, i))) =
    TauCeti.AlgHom.mapValue (rightParameterMap (K := K) n)
      (derivedInfinitesimalGroupWord n (fun i => d (true, i))) := by
  change (Bool × DerivedWordIndex n → Derivation K B (C (K := K) (B := B))) at d
  calc
    _ = derivedGroupWord n (fun i =>
        TauCeti.AlgHom.mapValue (rightParameterMap (K := K) n)
          (squareZeroTangentPoint (d (true, i))
            (infinitesimalWordLeaf K n i)
            (infinitesimalWordLeaf_sq_zero K n i))) := by
          congr 1
          funext i
          simpa only [rightParameterMap_leaf] using
            (squareZeroTangentPoint_map (d (true, i))
              (rightParameterMap (K := K) n)
              (infinitesimalWordLeaf K n i)
              (infinitesimalWordLeaf_sq_zero K n i)).symm
    _ = _ := by
      simpa only [derivedInfinitesimalGroupWord] using
        (derivedGroupWord_map
          (TauCeti.AlgHom.mapValue (rightParameterMap (K := K) n)) n
          (fun i => squareZeroTangentPoint (d (true, i))
            (infinitesimalWordLeaf K n i)
            (infinitesimalWordLeaf_sq_zero K n i))).symm

/-- The full mixed coefficient in a balanced group word is the
corresponding balanced tangent Lie word. -/
theorem derivedInfinitesimalGroupWord_eq_tangent (n : ℕ)
    (d : DerivedWordIndex n → Derivation K B (C (K := K) (B := B))) :
    derivedInfinitesimalGroupWord n d =
      squareZeroTangentPoint (derivedLieWord n d)
        (infinitesimalWordParameter K n)
        (infinitesimalWordParameter_sq_zero K n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [derivedInfinitesimalGroupWord, derivedGroupWord_succ]
      rw [leftBranch_word, rightBranch_word]
      rw [ih, ih]
      rw [squareZeroTangentPoint_map, squareZeroTangentPoint_map]
      rw [squareZeroTangentPoint_commutator]
      change squareZeroTangentPoint
          ⁅derivedLieWord n (fun i => d (false, i)),
            derivedLieWord n (fun i => d (true, i))⁆
          (leftParameterMap (K := K) n (infinitesimalWordParameter K n) *
            rightParameterMap (K := K) n (infinitesimalWordParameter K n)) _ =
        squareZeroTangentPoint
          ⁅derivedLieWord n (fun i => d (false, i)),
            derivedLieWord n (fun i => d (true, i))⁆
          (infinitesimalWordParameter K (n + 1)) _
      congr 1
      exact parameterMap_mul (K := K) n

end ReductiveGroups
