import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineSectionActions
import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineCoordinateSections

/-! # Affine pullback of the global endpoint section -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions
universe u

private theorem endpoint_polynomial (R : Type u) [CommRing R]
    (d : ℕ) (c b e a : R) :
    Polynomial.aeval (Polynomial.C c * Polynomial.X + Polynomial.C b)
        ((Polynomial.C e * Polynomial.X + Polynomial.C a) ^ d) =
      (Polynomial.C (e * c) * Polynomial.X + Polynomial.C (e * b + a)) ^ d := by
  simp only [map_pow, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.algebraMap_eq]
  congr 1
  ring

/-- Pullback substitutes the affine coordinate in the global endpoint section. -/
theorem projectiveAffineLineMap_endpoint (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b e a : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map
        (projectiveAffineEndpoint R d e a) ≫ projectiveAffineLineMap R d c b =
      (Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveAffineEndpoint R d (e * (c : R)) (e * b + a) := by
  refine projectiveAffineLineMap_section R d c b
    (projectiveAffineEndpoint R d e a)
    (projectiveAffineEndpoint R d (e * (c : R)) (e * b + a))
    ((Polynomial.C e * Polynomial.X + Polynomial.C a) ^ d)
    ((Polynomial.C (e * (c : R)) * Polynomial.X + Polynomial.C (e * b + a)) ^ d)
    (projectiveAffineEndpoint_left R d e a)
    (projectiveAffineEndpoint_left R d (e * (c : R)) (e * b + a)) ?_
  exact (projectiveAffineCoordinate_app R c b
    ((Polynomial.C e * Polynomial.X + Polynomial.C a) ^ d)).trans
    (congrArg (Scheme.ΓSpecIso (.of (Polynomial R))).inv
      (endpoint_polynomial R d (c : R) b e a))

end SchubertGeometry.ProjectiveLine
