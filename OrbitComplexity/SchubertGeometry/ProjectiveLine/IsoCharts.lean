import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsOverlap
import OrbitComplexity.GroupActions.Varieties.AdditiveOpens
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsReciprocal

/-! # Additive charts of the projective line

Each standard chart of the polynomial projective line has one affine coordinate.
The two additive charts cover the line, intersect in the punctured additive line,
and identify their nonzero parameters by inversion.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups TauCeti
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev lineIndex : Type u := ULift.{u} (Fin 2)
private theorem remainingUniqueExists (j : lineIndex.{u}) :
    Nonempty (Unique {a : lineIndex.{u} // a ≠ j}) := by
  rcases j with ⟨j⟩
  fin_cases j
  · refine ⟨{ default := ⟨⟨1⟩, by decide⟩, uniq := ?_ }⟩
    rintro ⟨⟨a⟩, ha⟩
    apply Subtype.ext
    apply ULift.ext
    fin_cases a <;> first | rfl | exact False.elim (ha rfl)
  · refine ⟨{ default := ⟨⟨0⟩, by decide⟩, uniq := ?_ }⟩
    rintro ⟨⟨a⟩, ha⟩
    apply Subtype.ext
    apply ULift.ext
    fin_cases a <;> first | rfl | exact False.elim (ha rfl)
private instance remainingUnique (j : lineIndex.{u}) :
    Unique {a : lineIndex.{u} // a ≠ j} := Classical.choice (remainingUniqueExists j)
variable (K : Type u) [Field K]
private def lineCoordinateEquiv (j : lineIndex.{u}) :
    SymmetricAlgebra K K ≃ₐ[K] MvPolynomial {a : lineIndex.{u} // a ≠ j} K :=
  SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton _ K)
private def lineAffineIso (j : lineIndex.{u}) : (additiveVariety K).toOver ≅
    (affineVariety K (MvPolynomial {a : lineIndex.{u} // a ≠ j} K)).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (lineCoordinateEquiv K j).symm).op

/-- A standard homogeneous-coordinate chart of the projective line, parametrized by Ga. -/
def projectiveLineChart (j : lineIndex.{u}) :
    (additiveVariety K).toOver ⟶ (projectiveVariety K lineIndex.{u}).toOver :=
  (lineAffineIso K j).hom ≫ projectiveChartMorphism K lineIndex.{u} j
/-- Each standard additive chart of the projective line is an open immersion. -/
instance projectiveLineChart_isOpen (j : lineIndex.{u}) :
    IsOpenImmersion (projectiveLineChart K j).left := by
  change IsOpenImmersion ((lineAffineIso K j).hom.left ≫
    (projectiveChartMorphism K lineIndex.{u} j).left)
  infer_instance
private theorem lineAffineIso_coordinate (j : lineIndex.{u})
    (a : {a : lineIndex.{u} // a ≠ j}) (t : K) :
    affineVarietyPointsEquiv K _ (Variety.mapPoints (lineAffineIso K j).hom
      (additivePointsEquiv K t)) (MvPolynomial.X a) = t := by
  let p := ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have ht : additivePointsEquiv K t = (affineVarietyPointsEquiv K _).symm p := rfl
  rw [ht]
  change affineVarietyPointsEquiv K _
    (Variety.mapPoints (affineMorphism (lineCoordinateEquiv K j).symm.toAlgHom)
      ((affineVarietyPointsEquiv K _).symm p)) (MvPolynomial.X a) = t
  rw [affineMorphism_points, Equiv.apply_symm_apply]
  change p ((lineCoordinateEquiv K j).symm (MvPolynomial.X a)) = t
  rw [lineCoordinateEquiv, SymmetricAlgebra.equivMvPolynomial_symm_X,
    Module.Basis.singleton_apply]
  exact AdditiveGroup.gaPointsMulEquiv_symm_apply_ι (Multiplicative.ofAdd t)

/-- The additive chart has the corresponding homogeneous-coordinate open as its image. -/
theorem projectiveLineChart_range (j : lineIndex.{u}) :
    (projectiveLineChart K j).left.opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} K) (MvPolynomial.X j) := by
  exact (Scheme.Hom.opensRange_comp_of_isIso (lineAffineIso K j).hom.left
    (projectiveChartMorphism K lineIndex.{u} j).left).trans (projectiveChartMap_range K _ j)
/-- The other standard chart pulls back to the punctured additive line. -/
theorem projectiveLineChart_preimage (j : lineIndex.{u}) (k : {k : lineIndex.{u} // k ≠ j}) :
    (projectiveLineChart K j).left ⁻¹ᵁ (projectiveLineChart K k.val).left.opensRange =
      additiveNonzero K := by
  rw [projectiveLineChart_range]
  change (lineAffineIso K j).hom.left ⁻¹ᵁ
    ((projectiveChartMorphism K lineIndex.{u} j).left ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} K)
        (MvPolynomial.X k.val)) = _
  have he : (projectiveChartMorphism K lineIndex.{u} j).left ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule lineIndex.{u} K)
        (MvPolynomial.X k.val) = PrimeSpectrum.basicOpen (MvPolynomial.X k) :=
    projectiveChartMap_preimage K lineIndex.{u} j k
  rw [he]
  change PrimeSpectrum.basicOpen ((lineCoordinateEquiv K j).symm (MvPolynomial.X k)) = _
  rw [lineCoordinateEquiv, SymmetricAlgebra.equivMvPolynomial_symm_X,
    Module.Basis.singleton_apply]
  rfl
/-- The two standard additive charts cover all scheme points of the projective line. -/
theorem projectiveLineChart_cover :
    Set.range (projectiveLineChart K ⟨0⟩).left ∪
      Set.range (projectiveLineChart K ⟨1⟩).left = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, y, hy⟩ := (projectiveChartCover K lineIndex.{u}).exists_eq x
  change lineIndex.{u} at j
  have hx : x ∈ (projectiveLineChart K j).left.opensRange := by
    rw [projectiveLineChart_range, ← projectiveChartMap_range]
    exact ⟨y, hy⟩
  rcases j with ⟨j⟩
  fin_cases j
  · exact Or.inl hx
  · exact Or.inr hx
variable [IsAlgClosed K]
/-- The second chart contains a first-chart rational point precisely off the origin. -/
theorem projectiveLineChart_overlap (t : K) :
    Variety.mapPoints (projectiveLineChart K ⟨0⟩) (additivePointsEquiv K t) ∈
      Set.range (Variety.mapPoints (projectiveLineChart K ⟨1⟩)) ↔ t ≠ 0 := by
  rw [Variety.range_mapPoints]
  simp only [Set.mem_preimage]
  rw [Variety.pointMap_mapPoints]
  change (additiveVariety K).pointMap (additivePointsEquiv K t) ∈
    ((projectiveLineChart K ⟨0⟩).left ⁻¹ᵁ
      (projectiveLineChart K ⟨1⟩).left.opensRange) ↔ t ≠ 0
  rw [projectiveLineChart_preimage K ⟨0⟩ ⟨⟨1⟩, by decide⟩]
  exact (mem_additiveNonzero K _).trans (by rw [Equiv.symm_apply_apply])
omit [IsAlgClosed K] in
private theorem affinePreimage_eval {A : Type u} [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] (p : (affineVariety K A).points) (a : A) :
    (Spec.preimage p.val).hom a = affineVarietyPointsEquiv K A p a := by
  obtain ⟨f, rfl⟩ := (affineVarietyPointsEquiv K A).symm.surjective p
  change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom a =
    (affinePointsEquiv.symm (affinePointsEquiv f)) a
  rw [Spec.preimage_map, Equiv.symm_apply_apply]
  rfl
omit [IsAlgClosed K] in
private theorem line_parameter_product (t b : K)
    (he : Variety.mapPoints (projectiveLineChart K ⟨0⟩) (additivePointsEquiv K t) =
      Variety.mapPoints (projectiveLineChart K ⟨1⟩) (additivePointsEquiv K b)) : t * b = 1 := by
  simp only [projectiveLineChart, Variety.mapPoints_comp] at he
  have hpq := congrArg Subtype.val he
  change (Variety.mapPoints (lineAffineIso K ⟨0⟩).hom (additivePointsEquiv K t)).val ≫
      projectiveChartMap K lineIndex.{u} ⟨0⟩ =
    (Variety.mapPoints (lineAffineIso K ⟨1⟩).hom (additivePointsEquiv K b)).val ≫
      projectiveChartMap K lineIndex.{u} ⟨1⟩ at hpq
  have hr := projectiveChart_reciprocal K lineIndex.{u} K ⟨0⟩ ⟨1⟩ (by decide)
    (Variety.mapPoints (lineAffineIso K ⟨0⟩).hom (additivePointsEquiv K t)).val
    (Variety.mapPoints (lineAffineIso K ⟨1⟩).hom (additivePointsEquiv K b)).val hpq
  rw [affinePreimage_eval, affinePreimage_eval,
    lineAffineIso_coordinate, lineAffineIso_coordinate] at hr
  exact hr

/-- The standard additive parameters of a common projective point are reciprocals. -/
theorem projectiveLineChart_transition {t : K} (ht : t ≠ 0) :
    Variety.mapPoints (projectiveLineChart K ⟨0⟩) (additivePointsEquiv K t) =
      Variety.mapPoints (projectiveLineChart K ⟨1⟩) (additivePointsEquiv K t⁻¹) := by
  obtain ⟨p, hp⟩ := (projectiveLineChart_overlap K t).mpr ht
  obtain ⟨b, rfl⟩ := (additivePointsEquiv K).surjective p
  have hr := line_parameter_product K t b hp.symm
  have hb : b = t⁻¹ := by
    apply mul_left_cancel₀ ht
    exact hr.trans (mul_inv_cancel₀ ht).symm
  rw [hb] at hp
  exact hp.symm
end SchubertGeometry
