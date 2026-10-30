import OrbitComplexity.SchubertGeometry.Cells.RichardsonDimension
import OrbitComplexity.SchubertGeometry.Normality.PositiveResolutionFibres
import OrbitComplexity.SchubertGeometry.Normality.PartialNormalDescent
import OrbitComplexity.GroupActions.Varieties.Normal
import OrbitComplexity.Paper.Deodhar.RichardsonOrbits
import OrbitComplexity.Paper.IntervalPolytopes
import OrbitComplexity.GroupActions.Complexity.MaxOrbit
import OrbitComplexity.SchubertGeometry.Cells.RichardsonSchubert
import OrbitComplexity.BruhatIntervals.Graph.Support
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Normality and torus complexity of Richardson and Schubert varieties

Schubert varieties in complete and partial flags and nonempty Richardson
varieties have normal local domains. The maximum orbit dimension and
Richardson dimension formula compute complexity; the lower-endpoint-one
case gives the Schubert support formula.
-/

open ReductiveGroups GroupActions SchubertGeometry BruhatIntervals
noncomputable section
namespace SchubertOrbits
universe u
/-- Schubert varieties in complete and partial flags, and Richardson varieties
with comparable endpoints, have integrally closed local domains. -/
theorem schubert_richardson_normality
    {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) :
    (∀ w : G.weylGroup, (schubertVariety G w).IsNormal) ∧
    (∀ (J : Set G.rootBase.support) (w : G.weylGroup),
      IsMinimalRightParabolic G.rootBase J w → (partialSchubertVariety G J w).IsNormal) ∧
    (∀ lower upper : G.weylGroup, (weylCoxeterSystem G.rootBase).BruhatLE lower upper →
      (richardsonVariety G lower upper).IsNormal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact @SchubertGeometry.schubert_normal_stalks.{u} K kField kClosed kZero G w
  · intro J w hw
    exact @SchubertGeometry.partialSchubert_normal_stalks.{u} K kField kClosed kZero G J w hw
  · intro lower upper hle
    exact @SchubertGeometry.richardson_normal_stalks.{u} K kField kClosed kZero G lower upper
      ((weyl_bruhat_iff G.rootBase lower upper).mpr hle)

/-- Complex Schubert varieties in complete and partial flags, and nonempty
complex Richardson varieties, have integrally closed local domains. -/
theorem schubert_richardson_normality_complex (G : ReductiveGroupData ℂ) :
    (∀ w : G.weylGroup, (schubertVariety G w).IsNormal) ∧
    (∀ (J : Set G.rootBase.support) (w : G.weylGroup),
      IsMinimalRightParabolic G.rootBase J w → (partialSchubertVariety G J w).IsNormal) ∧
    (∀ lower upper : G.weylGroup, (weylCoxeterSystem G.rootBase).BruhatLE lower upper →
      (richardsonVariety G lower upper).IsNormal) :=
  @schubert_richardson_normality.{0} ℂ inferInstance inferInstance inferInstance G

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Richardson torus complexity is the endpoint length difference minus interval dimension. -/
theorem richardson_torus_complexity (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    torusComplexity G (richardsonVariety G a b) =
      (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a -
        algebraicDim (weylRealization G.rootBase) a b := by
  obtain ⟨x, hx⟩ := (richardson_orbit_maximum G a b hle).1
  change minOrbitCodim (torusVariety G) (richardsonVariety G a b) = _
  rw [minOrbitCodim_eq_sub_max (torusVariety G) (richardsonVariety G a b)
    (algebraicDim (weylRealization G.rootBase) a b) (richardson_orbit_le G a b) x hx,
      richardsonVariety_natDim G a b hle]

/-- The numerical Richardson complexity formula over the complex numbers. -/
theorem richardson_torus_complexity_complex (G : ReductiveGroupData ℂ) (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    torusComplexity G (richardsonVariety G a b) =
      (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a -
        algebraicDim (weylRealization G.rootBase) a b := by
  have hmax := richardson_orbit_maximum_complex G a b hle
  obtain ⟨x, hx⟩ := hmax.1
  change minOrbitCodim (torusVariety G) (richardsonVariety G a b) = _
  exact (@minOrbitCodim_eq_sub_max ℂ inferInstance (torusVariety G)
    (richardsonVariety G a b) inferInstance inferInstance
    (algebraicDim (weylRealization G.rootBase) a b)
    (fun y => hmax.2 ⟨y, rfl⟩) x hx).trans
      (congrArg (fun n : ℕ => n - algebraicDim (weylRealization G.rootBase) a b)
        (richardsonVariety_natDim G a b hle))

/-- Schubert torus complexity is Coxeter length minus support cardinality. -/
theorem schubert_torus_complexity (w : G.weylGroup) :
    torusComplexity G (schubertVariety G w) =
      (weylCoxeterSystem G.rootBase).length w - supportCard (weylCoxeterSystem G.rootBase) w := by
  have h := richardson_torus_complexity G 1 w ((weylCoxeterSystem G.rootBase).one_bruhatLE w)
  rwa [torus_richardson_one_complexity, (weylCoxeterSystem G.rootBase).length_one,
    Nat.sub_zero, algebraicDim_one] at h

/-- The Schubert length-minus-support complexity formula over the complex numbers. -/
theorem schubert_torus_complexity_complex (G : ReductiveGroupData ℂ) (w : G.weylGroup) :
    torusComplexity G (schubertVariety G w) =
      (weylCoxeterSystem G.rootBase).length w - supportCard (weylCoxeterSystem G.rootBase) w := by
  have h := richardson_torus_complexity_complex G 1 w
    ((weylCoxeterSystem G.rootBase).one_bruhatLE w)
  rwa [torus_richardson_one_complexity, (weylCoxeterSystem G.rootBase).length_one,
    Nat.sub_zero, algebraicDim_one] at h

end SchubertOrbits
