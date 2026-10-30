import OrbitComplexity.SchubertGeometry.LineBundles.Affine.EndpointAction
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.AssociatedPullbacks
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Endpoint

/-! # The endpoint section in the rank-one character line -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups
universe u

/-- The normalized endpoint pulls back to the endpoint with the affine coefficients. -/
theorem projectiveAffineLineMap_endpoint_one (R : Type u) [CommRing R]
    (d : ℕ) (c : Rˣ) (b : R) :
    (Scheme.Modules.pullback (projectiveAffineMorphism R c b)).map
        (projectiveAffineEndpoint R d 1 0) ≫ projectiveAffineLineMap R d c b =
      (Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism R c b)).hom ≫
        projectiveAffineEndpoint R d (c : R) b := by
  simpa only [one_mul, add_zero] using
    projectiveAffineLineMap_endpoint R d c b 1 0

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The transported affine pullback of the endpoint is the transformed endpoint section. -/
theorem determinantEndpoint_pullback (N : ℕ) (i : G.rootBase.support)
    (c : Kˣ) (b : K) :
    (Scheme.Modules.pullback (projectiveAffineMorphism K c b)).map
        (SchubertGeometry.ProjectiveLine.determinantEndpoint G N i) ≫
      (Scheme.Modules.pullback (projectiveAffineMorphism K c b)).map
        (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).hom ≫
      projectiveAffineLineMap K (2 * N) c b ≫ (SchubertGeometry.ProjectiveLine.characterPowerLineIso
        G N i).inv =
    (Scheme.Modules.pullbackObjUnitIso (projectiveAffineMorphism K c b)).hom ≫
      projectiveAffineEndpoint K (2 * N) (c : K) b ≫
        (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).inv := by
  erw [← Functor.map_comp_assoc, SchubertGeometry.ProjectiveLine.determinantEndpoint_image]
  convert! congrArg
    (fun t => t ≫ (SchubertGeometry.ProjectiveLine.characterPowerLineIso G N i).inv)
    (projectiveAffineLineMap_endpoint_one K (2 * N) c b) using 1

end SchubertGeometry.ProjectiveLine
