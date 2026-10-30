import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Coaction
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-! # The opposite-Borel eigenline of the determinant functional -/

open ReductiveGroups TauCeti GroupActions

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borel_conjugate_le (b : G.points) (hb : b ∈ G.borelPoints) :
    G.borelIdeal.conjugate b ≤ G.borelIdeal := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  let : IsReduced G.borelAlgebra := isReduced_of_smooth K G.borelAlgebra
  let : IsReduced (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal) :=
    inferInstanceAs (IsReduced G.borelAlgebra)
  apply HopfIdeal.le_of_quotientPointsSubgroup_le
    (H := CommHopfAlgCat.of K G.coordinateAlgebra) (K := K)
  intro x hx
  have hm : b⁻¹ * x * b ∈ G.borelPoints :=
    G.borelPoints.mul_mem (G.borelPoints.mul_mem (G.borelPoints.inv_mem hb) hx) hb
  have h := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff
    G.borelIdeal b (CommAlgCat.of K K) (b⁻¹ * x * b)).mpr hm
  simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
    AlgHom.mapValue_id, MonoidHom.id_apply, mul_assoc, mul_inv_cancel_left,
    mul_inv_cancel, mul_one] using h

omit [CharZero K] in
private theorem borel_conjugate_eq (b : G.points) (hb : b ∈ G.borelPoints) :
    G.borelIdeal.conjugate b = G.borelIdeal := by
  apply le_antisymm (borel_conjugate_le G b hb)
  have h := HopfIdeal.conjugate_mono b (borel_conjugate_le G b⁻¹
    (G.borelPoints.inv_mem hb))
  simpa using h

omit [CharZero K] in
private theorem borel_tangent_stable (b : G.points) (hb : b ∈ G.borelPoints)
    (x : G.tangent) (hx : x ∈ G.borelTangent) :
    affineGroupAdjointRepresentation b x ∈ G.borelTangent := by
  have h := adjoint_mem_conjugate_tangent G.borelIdeal b x hx
  rw [borel_conjugate_eq G b hb] at h
  exact h

omit [IsAlgClosed K] [CharZero K] in
private theorem projection_functional_eigen {V : Type u} [AddCommGroup V] [Module K V]
    (F C : Submodule K V) [Module.Finite K F] (h : IsCompl F C)
    (f : Module.End K V) (hs : ∀ x ∈ C, f x ∈ C) :
    ∃ c : K,
      ((exteriorPower.topEquiv (Module.finBasis K F)).toLinearMap.comp
        (exteriorPower.map (Module.finrank K F) (F.projectionOnto C h))).comp
          (exteriorPower.map (Module.finrank K F) f) =
      c • ((exteriorPower.topEquiv (Module.finBasis K F)).toLinearMap.comp
        (exteriorPower.map (Module.finrank K F) (F.projectionOnto C h))) := by
  let P := F.projectionOnto C h
  let a : Module.End K F := (P.comp f).comp F.subtype
  have hp : P.comp f = a.comp P := by
    apply LinearMap.ext
    intro x
    have hx : x - F.subtype (P x) ∈ C := Submodule.sub_projection_mem h x
    have hz : P (f (x - F.subtype (P x))) = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff h).mpr (hs _ hx)
    simp only [map_sub] at hz
    exact sub_eq_zero.mp hz
  refine ⟨LinearMap.det a, ?_⟩
  apply LinearMap.ext
  intro x
  change exteriorPower.topEquiv (Module.finBasis K F)
      (exteriorPower.map _ P (exteriorPower.map _ f x)) =
    LinearMap.det a • exteriorPower.topEquiv (Module.finBasis K F)
      (exteriorPower.map _ P x)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hp,
    exteriorPower.map_comp, LinearMap.comp_apply,
    exteriorPower.map_finrank_eq_det_smul, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- The functional defining the coefficient is an eigenvector for the Borel
conjugated by the inverse longest representative, the complement used in its definition. -/
theorem positiveDet_oppositeBorel_eigen (b : G.points) (hb : b ∈ G.borelPoints) :
    ∃ c : K, (positiveDetFunctional G).comp
        (exteriorPower.map (Module.finrank K G.unipotentTangent)
          (affineGroupAdjointRepresentation (G.longestPoint⁻¹ * b * G.longestPoint))) =
      c • positiveDetFunctional G := by
  unfold positiveDetFunctional
  apply projection_functional_eigen
  intro x hx
  change x ∈ G.borelTangent.toSubmodule.map
    (affineGroupAdjointLieEquiv G.longestPoint).toLinearEquiv.symm.toLinearMap at hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  apply Submodule.mem_map.mpr
  refine ⟨affineGroupAdjointRepresentation b y, borel_tangent_stable G b hb y hy, ?_⟩
  change affineGroupAdjointRepresentation G.longestPoint⁻¹
      (affineGroupAdjointRepresentation b y) =
    affineGroupAdjointRepresentation (G.longestPoint⁻¹ * b * G.longestPoint)
      (affineGroupAdjointRepresentation G.longestPoint⁻¹ y)
  have hw : affineGroupAdjointRepresentation G.longestPoint
      (affineGroupAdjointRepresentation G.longestPoint⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw]

end SchubertGeometry.DeterminantSection
