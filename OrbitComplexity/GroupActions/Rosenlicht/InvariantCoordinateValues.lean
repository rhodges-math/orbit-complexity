import OrbitComplexity.GroupActions.Rosenlicht.InvariantCoordinates
import OrbitComplexity.GroupActions.Rosenlicht.OpenPointValues

/-!
# Values of invariant coordinates

Points with the same invariant-map image have equal values on its pulled-back coordinate
algebra.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- Coordinates of the affine invariant-field model pull back to sections on
the domain of the invariant morphism. -/
def invariantCoordinates :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : Algebra.EssFiniteType K (invariantField H X) := invariantField_essFiniteType H X
    fieldModelAlgebra K (invariantField H X) →+* Γ(X.scheme, (invariantMap H X).domain) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  let A := fieldModelAlgebra K (invariantField H X)
  exact ((Scheme.ΓSpecIso (.of A)).inv ≫ (invariantMorphism H X).left.appTop ≫
    (invariantMap H X).domain.topIso.hom).hom

/-- Rational points with the same invariant-morphism image give equal values
on every coordinate pulled back from the invariant-field model. -/
theorem invariantCoordinates_values (x y : X.points)
    (hx : X.pointMap x ∈ (invariantMap H X).domain)
    (hy : X.pointMap y ∈ (invariantMap H X).domain)
    (he : (invariantMorphism H X).left ⟨X.pointMap x, hx⟩ =
      (invariantMorphism H X).left ⟨X.pointMap y, hy⟩) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : Algebra.EssFiniteType K (invariantField H X) := invariantField_essFiniteType H X
    (openPointEval X _ (pointInOpen X _ x hx)).comp (invariantCoordinates H X) =
      (openPointEval X _ (pointInOpen X _ y hy)).comp (invariantCoordinates H X) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  let D := (invariantMap H X).domain
  let p : (invariantDomain H X).points := pointInOpen X D x hx
  let q : (invariantDomain H X).points := pointInOpen X D y hy
  have hp : (invariantDomain H X).pointMap p = ⟨X.pointMap x, hx⟩ := by
    apply Subtype.ext
    exact congrArg (fun f : Spec (.of K) ⟶ X.scheme ↦ f (IsLocalRing.closedPoint K))
      (congrArg Subtype.val (mapPoints_pointInOpen X D x hx))
  have hq : (invariantDomain H X).pointMap q = ⟨X.pointMap y, hy⟩ := by
    apply Subtype.ext
    exact congrArg (fun f : Spec (.of K) ⟶ X.scheme ↦ f (IsLocalRing.closedPoint K))
      (congrArg Subtype.val (mapPoints_pointInOpen X D y hy))
  have hpoints : mapPoints (invariantMorphism H X) p =
      mapPoints (invariantMorphism H X) q := by
    apply (invariantModel H X).pointMap_injective
    rw [pointMap_mapPoints, pointMap_mapPoints, hp, hq]
    exact he
  let A := fieldModelAlgebra K (invariantField H X)
  let p' : Spec (.of K) ⟶ D.toScheme := p.val
  let q' : Spec (.of K) ⟶ D.toScheme := q.val
  let f : D.toScheme ⟶ Spec (.of A) := (invariantMorphism H X).left
  have hraw : p' ≫ f = q' ≫ f := congrArg Subtype.val hpoints
  have happ := congrArg (fun f : Spec (.of K) ⟶ Spec (.of A) ↦ f.appTop) hraw
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at happ
  ext a
  change (Scheme.ΓSpecIso (.of K)).hom
      (p'.appTop (D.topIso.inv (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a))))) =
    (Scheme.ΓSpecIso (.of K)).hom
      (q'.appTop (D.topIso.inv (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)))))
  rw [show D.topIso.inv (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
      f.appTop ((Scheme.ΓSpecIso (.of A)).inv a) from
      D.topIso.commRingCatIsoToRingEquiv.left_inv _]
  exact congrArg (fun g : Γ(Spec (.of A), ⊤) ⟶ Γ(Spec (.of K), ⊤) ↦
    (Scheme.ΓSpecIso (.of K)).hom (g ((Scheme.ΓSpecIso (.of A)).inv a))) happ

end

end GroupActions.Variety
