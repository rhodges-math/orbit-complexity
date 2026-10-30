import OrbitComplexity.GroupActions.Rosenlicht.AffineOpenPoints

/-!
# OpenValues
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

private theorem pointRange_subset (U : X.scheme.Opens) (x : X.points)
    (hx : X.pointMap x ∈ U) : Set.range x.val ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  rintro z ⟨t, rfl⟩
  change x.val t ∈ U
  change x.val (IsLocalRing.closedPoint K) ∈ U at hx
  simpa only [Subsingleton.elim t (IsLocalRing.closedPoint K)] using hx

/-- A rational point lying in an open subset has a unique lifted rational point. -/
def pointInOpen (U : X.scheme.Opens) (x : X.points) (hx : X.pointMap x ∈ U) :
    (X.openSubvariety U).points := by
  letI : IsOpenImmersion U.ι := X.openInclusion_isOpenImmersion U
  let x' : Spec (.of K) ⟶ X.scheme := x.val
  let t : Spec (.of K) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι x' (pointRange_subset X U x hx)
  refine ⟨t, ?_⟩
  change t ≫ (U.ι ≫ X.toSpec) = 𝟙 _
  rw [← Category.assoc]
  have ht : t ≫ U.ι = x' := IsOpenImmersion.lift_fac U.ι x' _
  rw [ht]
  exact x.property

/-- The lifted point maps to its original point under the open inclusion. -/
theorem mapPoints_pointInOpen (U : X.scheme.Opens) (x : X.points)
    (hx : X.pointMap x ∈ U) :
    mapPoints (X.openInclusion U) (pointInOpen X U x hx) = x := by
  apply Subtype.ext
  have : IsOpenImmersion U.ι := X.openInclusion_isOpenImmersion U
  change (pointInOpen X U x hx).val ≫ U.ι = x.val
  dsimp only [pointInOpen]
  exact IsOpenImmersion.lift_fac U.ι x.val _

/-- A regular section on an affine open evaluates at each rational point in that open. -/
def regularValue (U : X.scheme.Opens) (hU : IsAffineOpen U) (x : X.points)
    (hx : X.pointMap x ∈ U) : Γ(X.scheme, U) →+* K :=
  affineOpenPointEval X U hU (pointInOpen X U x hx)

end

end GroupActions.Variety
