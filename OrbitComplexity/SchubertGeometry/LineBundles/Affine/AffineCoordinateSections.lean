import OrbitComplexity.SchubertGeometry.LineBundles.Affine.AffineChartAction

/-! Pullback of polynomial-chart sections. -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory
universe u

private theorem spec_polynomial_apply (R : Type u) [CommRing R]
    (e : Polynomial R →+* Polynomial R) (r : Polynomial R) :
    (Spec.map (CommRingCat.ofHom e)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (e r) :=
  (congrArg (fun h => h r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm

/-- The invariant-chart pullback substitutes cX+b in every polynomial section. -/
theorem projectiveAffineCoordinate_app (R : Type u) [CommRing R]
    (c : Rˣ) (b : R) (r : Polynomial R) :
    (projectiveAffineCoordinate R c b).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((Polynomial.aeval (Polynomial.C (c : R) * Polynomial.X + Polynomial.C b)) r) := by
  let es := Polynomial.algEquivCMulXAddC (c : R) 0
  let et := Polynomial.algEquivAevalXAddC b
  have he : es.toAlgHom.comp et.toAlgHom =
      Polynomial.aeval (Polynomial.C (c : R) * Polynomial.X + Polynomial.C b) := by
    ext
    simp [es, et, Polynomial.algEquivAevalXAddC_apply, Polynomial.algEquivCMulXAddC_apply]
  change (Spec.map (CommRingCat.ofHom es.toRingHom)).appTop
      ((Spec.map (CommRingCat.ofHom et.toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv r)) = _
  rw [spec_polynomial_apply, spec_polynomial_apply]
  exact congrArg (Scheme.ΓSpecIso (.of (Polynomial R))).inv
    (congrArg (fun q : Polynomial R →ₐ[R] Polynomial R => q r) he)

end SchubertGeometry.ProjectiveLine
