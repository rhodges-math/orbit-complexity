import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Torus
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTorusUnipotent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Reduced

/-! # The determinant line under the Borel and unipotent groups -/

open ReductiveGroups TauCeti GroupActions
open scoped TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem unipotent_stable (g : G.points) (hg : g ∈ G.borelPoints)
    (x : G.unipotentTangent) :
    affineGroupAdjointRepresentation g (x : G.tangent) ∈ G.unipotentTangent := by
  apply (tangent_mem_hopfQuotient_iff G.unipotentIdeal _).mpr
  intro a ha
  have hi : affineGroupConjugationBialgHom g a ∈ G.unipotentIdeal :=
    BorelRootUnipotentHopfIdeal.borel_point_conjugation
      G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
      G.torusSplit G.split_surjective G.split_eq_zero G.reductive g hg a ha
  have hx := (tangent_mem_hopfQuotient_iff G.unipotentIdeal (x : G.tangent)).mp x.property
  have hd : affineGroupAdjointRepresentation g (x : G.tangent) =
      derivationComp (B := K) (affineGroupConjugationBialgHom g) (x : G.tangent) := by
    simpa only [affineGroupAdjointRepresentation_apply] using
      (DerivationComp.conjugation g (x : G.tangent)).symm
  rw [hd]
  exact hx _ hi

private def unipotentEnd (g : G.points) (hg : g ∈ G.borelPoints) :
    Module.End K G.unipotentTangent :=
  LinearMap.codRestrict G.unipotentTangent.toSubmodule
    ((affineGroupAdjointRepresentation g).comp G.unipotentTangent.toSubmodule.subtype)
    (unipotent_stable G g hg)

omit [IsAlgClosed K] [CharZero K] in
private theorem determinant_vector_stable {V : Type u} [AddCommGroup V] [Module K V]
    (F : Submodule K V) [Module.Finite K F]
    (a : Module.End K F) (b : Module.End K V)
    (hc : F.subtype.comp a = b.comp F.subtype) :
    exteriorPower.map (Module.finrank K F) b
        (exteriorPower.map (Module.finrank K F) F.subtype
          (exteriorPower.ιMulti K _ (Module.finBasis K F))) =
      LinearMap.det a • exteriorPower.map (Module.finrank K F) F.subtype
        (exteriorPower.ιMulti K _ (Module.finBasis K F)) := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, ← hc,
    exteriorPower.map_comp, LinearMap.comp_apply, exteriorPower.map_finrank_eq_det_smul,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- Every Borel point preserves the positive determinant line. -/
theorem positiveDet_borel_eigen (g : G.points) (hg : g ∈ G.borelPoints) :
    letI := adjointExteriorComodule G
    ∃ c : K, Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _
      g (positiveDetVector G) = c • positiveDetVector G := by
  refine ⟨LinearMap.det (unipotentEnd G g hg), ?_⟩
  rw [adjointExterior_points]
  exact determinant_vector_stable G.unipotentTangent.toSubmodule
    (unipotentEnd G g hg) (affineGroupAdjointRepresentation g) rfl

private theorem unipotent_point (g : G.points) (hg : g ∈ G.unipotentPoints) :
    HopfAlgebra.IsUnipotentPoint g := by
  let : Algebra.Smooth K G.unipotentAlgebra := G.unipotent_smooth
  let : IsReduced G.unipotentAlgebra := isReduced_of_smooth K G.unipotentAlgebra
  change ∃ u, (CommHopfAlgCat.quotientPointsHom (CommHopfAlgCat.of K G.coordinateAlgebra)
    G.unipotentIdeal (CommAlgCat.of K K)) u = g at hg
  obtain ⟨u, hu⟩ := hg
  have hU := geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint
    G.unipotent_geometricallyUnipotent u
  have h := hU.mapDomain
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra) G.unipotentIdeal).hom
  change HopfAlgebra.IsUnipotentPoint
    ((CommHopfAlgCat.quotientPointsHom (CommHopfAlgCat.of K G.coordinateAlgebra)
      G.unipotentIdeal (CommAlgCat.of K K)) u) at h
  rwa [hu] at h

omit [IsAlgClosed K] [CharZero K] in
private theorem unipotent_eigenvalue {V : Type u} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hn : IsNilpotent (f - 1))
    {v : V} (hv : v ≠ 0) {c : K} (hc : f v = c • v) : c = 1 := by
  obtain ⟨n, hn⟩ := hn
  have hs : (f - 1) v = (c - 1) • v := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, hc, sub_smul, one_smul]
  have hp (m : ℕ) : ((f - 1) ^ m) v = (c - 1) ^ m • v := by
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          ((f - 1) ^ (m + 1)) v = (f - 1) (((f - 1) ^ m) v) := by
            rw [pow_succ', Module.End.mul_apply]
          _ = (f - 1) ((c - 1) ^ m • v) := by rw [ih]
          _ = (c - 1) ^ m • ((f - 1) v) := map_smul _ _ _
          _ = (c - 1) ^ (m + 1) • v := by rw [hs, smul_smul, ← pow_succ]
  have hz : (c - 1) ^ n • v = 0 := by rw [← hp, hn, LinearMap.zero_apply]
  have hcz : (c - 1) ^ n = 0 := (smul_eq_zero.mp hz).resolve_right hv
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hcz)

/-- The positive-unipotent subgroup fixes the positive determinant vector. -/
theorem positiveDet_unipotent (g : G.points) (hg : g ∈ G.unipotentPoints) :
    letI := adjointExteriorComodule G
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _
      g (positiveDetVector G) = positiveDetVector G := by
  let := adjointExteriorComodule G
  let E := ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent
  let M := FGComoduleCat.of (R := K) (C := G.coordinateAlgebra) E
  obtain ⟨c, hc⟩ := positiveDet_borel_eigen G g (G.unipotent_le_borel hg)
  have hu := unipotent_point G g hg M
  have hw : (1 ⊗ₜ[K] positiveDetVector G : K ⊗[K] M) ≠ 0 := by
    intro h
    have hz := congrArg (TensorProduct.lid K M) h
    exact positiveDet_ne_zero G (by simpa only [TensorProduct.lid_tmul,
      one_smul, map_zero] using hz)
  have he :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End K (K ⊗[K] M)) (1 ⊗ₜ[K] positiveDetVector G) =
      c • (1 ⊗ₜ[K] positiveDetVector G) := by
    change (Comodule.pointsAction M g).toLinearMap _ = _
    rw [Comodule.pointsAction_toLinearMap, Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation, hc]
    simp
  rw [LinearMap.GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff] at hu
  have hcone : c = 1 := unipotent_eigenvalue _ hu hw he
  simpa only [hcone, one_smul] using hc

/-- The constructed regular determinant coefficient is invariant under right-U translation. -/
theorem positiveDet_right_unipotent (g u : G.points) (hu : u ∈ G.unipotentPoints) :
    (g * u).ofConv (positiveDetCoefficient G) = g.ofConv (positiveDetCoefficient G) := by
  let := adjointExteriorComodule G
  change (g * u).ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G)) =
    g.ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G))
  rw [Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient,
    map_mul, Module.End.mul_apply, positiveDet_unipotent G u hu]

end SchubertGeometry.DeterminantSection
