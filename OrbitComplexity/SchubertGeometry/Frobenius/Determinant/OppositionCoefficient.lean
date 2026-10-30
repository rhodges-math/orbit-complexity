import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionComplement
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussPolynomial
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Power
import Batteries.Tactic.Lint

/-!
# The coefficient on the translated opposition chart

The complementary root factor is absorbed by left opposite-unipotent
invariance. The remaining specified simple-root parameter contributes its
square, with a constant torus unit.
-/

open ReductiveGroups TauCeti GroupActions

noncomputable section

namespace SchubertGeometry.DeterminantSection

private theorem translated_factor {M : Type*} [Group M]
    (w c u x y s b : M) (hy : c * x * c⁻¹ = y)
    (hc : c * w⁻¹ = s * b) :
    (c * w⁻¹) * (w * (u * x) * w⁻¹) =
      (c * u * c⁻¹) * ((y * s) * b) := by
  calc
    _ = (c * u * c⁻¹) * ((c * x * c⁻¹) * (c * w⁻¹)) := by group
    _ = (c * u * c⁻¹) * ((y * s) * b) := by rw [hy, hc, mul_assoc y s b]

private theorem sign_square {R : Type*} [CommRing R]
    (ε t : R) (hε : ε = 1 ∨ ε = -1) : (ε * t) ^ 2 = t ^ 2 := by
  rcases hε with rfl | rfl <;> simp

private theorem nonzero_of_inverse {M R : Type*} [Group M]
    [CommRing R] [Nontrivial R] (F : M → R) (h1 : F 1 = 1)
    (b : M) (h : F (b⁻¹ * b) = F b * F b⁻¹) : F b ≠ 0 := by
  intro hz
  have hinv : F (b⁻¹ * b) = 1 := (congrArg F (inv_mul_cancel b)).trans h1
  rw [hz, zero_mul] at h
  exact zero_ne_one (h.symm.trans hinv)

private theorem evaluation_power {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (p : A →ₐ[R] R) (q : A) (a t : R) (h : p q = a * t ^ 2) (N : ℕ) :
    p (q ^ N) = a ^ N * t ^ (2 * N) := by
  calc
    _ = (p q) ^ N := map_pow p q N
    _ = (a * t ^ 2) ^ N := congrArg (fun z : R => z ^ N) h
    _ = a ^ N * (t ^ 2) ^ N := mul_pow _ _ _
    _ = a ^ N * t ^ (2 * N) :=
      congrArg (fun z : R => a ^ N * z) (pow_mul t 2 N).symm

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

/-- The group lift of the translated simple opposition coordinates. -/
def oppositionRootLift (i : G.rootBase.support) (u : G.points) (t : K) : G.points :=
  oppositionChartPoint G i *
    (G.longestPoint * (u * gaParameterPoint (G.simpleRootMap i) t) * G.longestPoint⁻¹)

private theorem rootLift_coefficient (i : G.rootBase.support)
    (ε : K) (hε : ε = 1 ∨ ε = -1)
    (hparameter : ∀ t : K,
      oppositionConjugator G i * gaParameterPoint (G.simpleRootMap i) t *
          (oppositionConjugator G i)⁻¹ =
        gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t))
    (b : G.points) (hb : b ∈ G.torusPoints)
    (hchart : oppositionChartPoint G i =
      (G.reflectionPoint (oppositionSimple G i).val)⁻¹ * b)
    (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) (t : K) :
    (oppositionRootLift G i u t).ofConv (positiveDetCoefficient G) =
      b.ofConv (positiveDetCoefficient G) * t ^ 2 := by
  have hfactor := translated_factor G.longestPoint (oppositionConjugator G i) u
    (gaParameterPoint (G.simpleRootMap i) t)
    (gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t))
    (G.reflectionPoint (oppositionSimple G i).val)⁻¹ b (hparameter t) hchart
  have hleft := positiveDet_left_unipotent G
    (oppositionConjugator G i * u * (oppositionConjugator G i)⁻¹)
    ((gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t) *
      (G.reflectionPoint (oppositionSimple G i).val)⁻¹) * b)
    (oppositionComplement_mem G i u hu)
  have hright := positiveDet_right_borel G
    (gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t) *
      (G.reflectionPoint (oppositionSimple G i).val)⁻¹) b (G.torus_le_borel hb)
  calc
    _ = _ := congrArg (fun p : G.points => p.ofConv (positiveDetCoefficient G)) hfactor
    _ = _ := hleft
    _ = _ := hright
    _ = b.ofConv (positiveDetCoefficient G) * (ε * t) ^ 2 :=
      congrArg (fun z : K => b.ofConv (positiveDetCoefficient G) * z)
        (positiveDet_simple_frame G (oppositionSimple G i) (ε * t))
    _ = _ := congrArg (fun z : K => b.ofConv (positiveDetCoefficient G) * z)
      (sign_square ε t hε)

/-- On the full translated simple chart, every coefficient power is a constant
unit times the corresponding even power of its transverse coordinate. -/
theorem oppositionRootLift_coefficient (i : G.rootBase.support) :
    ∃ a : Kˣ, ∀ (N : ℕ) (u : G.points)
      (_ : u ∈ G.rootSubsetPoints
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i))) (t : K),
      (oppositionRootLift G i u t).ofConv (positiveDetPower G N) =
        (a : K) ^ N * t ^ (2 * N) := by
  obtain ⟨ε, hε, hparameter⟩ := oppositionSimple_parameter G i
  obtain ⟨b, hb, hchart⟩ := oppositionChartPoint_torus G i
  have hn : b.ofConv (positiveDetCoefficient G) ≠ 0 :=
    nonzero_of_inverse (fun p : G.points => p.ofConv (positiveDetCoefficient G))
      (positiveDet_counit G) b
      (positiveDet_right_borel G b⁻¹ b (G.torus_le_borel hb))
  let a : Kˣ := Units.mk0 (b.ofConv (positiveDetCoefficient G)) hn
  refine ⟨a, ?_⟩
  intro N u hu t
  exact evaluation_power (oppositionRootLift G i u t).ofConv
    (positiveDetCoefficient G) (a : K) t
    (rootLift_coefficient G i ε hε hparameter b hb hchart u hu t) N

end SchubertGeometry.DeterminantSection
