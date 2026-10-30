import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Functional
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatSystem

/-! # left opposite-unipotent invariance of the determinant coefficient -/

open ReductiveGroups TauCeti GroupActions
open scoped TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem longest_square_borel :
    G.longestPoint * G.longestPoint ∈ G.borelPoints := by
  obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.weylElementPoint_mul
    G.rootBase G.longestElement G.longestElement
  have hlong : G.longestElement * G.longestElement = 1 :=
    longestWeylElement_sq G.rootBase
  have he' : G.longestPoint * G.longestPoint = t := by
    change G.weylPoint G.longestElement * G.weylPoint G.longestElement = t
    simpa only [G.weylPoint_eq, hlong, weylElementPoint_one, mul_one] using he
  rw [he']
  exact G.torus_le_borel ht

private theorem opposite_conjugate_borel (u : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) :
    G.longestPoint * u * G.longestPoint⁻¹ ∈ G.borelPoints := by
  have hx : G.longestPoint⁻¹ * u * G.longestPoint ∈ G.unipotentPoints := by
    apply (G.conj_mem_oppositeUnipotent _).mp
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hu
  have hb := G.borelPoints.mul_mem
    (G.borelPoints.mul_mem (longest_square_borel G) (G.unipotent_le_borel hx))
      (G.borelPoints.inv_mem (longest_square_borel G))
  have he : (G.longestPoint * G.longestPoint) *
      (G.longestPoint⁻¹ * u * G.longestPoint) *
        (G.longestPoint * G.longestPoint)⁻¹ =
      G.longestPoint * u * G.longestPoint⁻¹ := by group
  rwa [he] at hb

private theorem opposite_unipotent_point (u : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) : HopfAlgebra.IsUnipotentPoint u := by
  let : Algebra.Smooth K G.oppositeUnipotentAlgebra := G.oppositeUnipotent_smooth
  let : IsReduced G.oppositeUnipotentAlgebra :=
    isReduced_of_smooth K G.oppositeUnipotentAlgebra
  change ∃ uq, (CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj
    G.oppositeUnipotentIdeal (CommAlgCat.of K K)) uq = u at hu
  obtain ⟨uq, he⟩ := hu
  have hU := geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint
    G.oppositeUnipotent_geometricallyUnipotent uq
  have h := hU.mapDomain
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.oppositeUnipotentIdeal).hom
  change HopfAlgebra.IsUnipotentPoint
    ((CommHopfAlgCat.quotientPointsHom G.coordinateAlgebra.obj
      G.oppositeUnipotentIdeal (CommAlgCat.of K K)) uq) at h
  rwa [he] at h

omit [IsAlgClosed K] [CharZero K] in
private theorem functional_unipotent_scalar {V : Type u} [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hn : IsNilpotent (f - 1))
    (φ : V →ₗ[K] K) (w : V) (hw : φ w = 1) (c : K)
    (hc : φ.comp f = c • φ) : c = 1 := by
  have hs (x : V) : φ ((f - 1) x) = (c - 1) * φ x := by
    have he := LinearMap.congr_fun hc x
    change φ (f x) = c * φ x at he
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    ring
  have hp (n : ℕ) (x : V) : φ (((f - 1) ^ n) x) = (c - 1) ^ n * φ x := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, hs, ih, pow_succ]
        ring
  obtain ⟨n, hn⟩ := hn
  have hz := hp n w
  rw [hn, LinearMap.zero_apply, map_zero, hw, mul_one] at hz
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz.symm)

/-- The opposite-unipotent subgroup fixes the defining determinant functional. -/
theorem positiveDet_oppositeUnipotent (u : G.points) (hu : u ∈ G.oppositeUnipotentPoints) :
    (positiveDetFunctional G).comp
        (exteriorPower.map (Module.finrank K G.unipotentTangent)
          (affineGroupAdjointRepresentation u)) = positiveDetFunctional G := by
  let := adjointExteriorComodule G
  let E := ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent
  let M := FGComoduleCat.of (R := K) (C := G.coordinateAlgebra) E
  let b := G.longestPoint * u * G.longestPoint⁻¹
  obtain ⟨c, hc⟩ := positiveDet_oppositeBorel_eigen G b
    (opposite_conjugate_borel G u hu)
  have he : G.longestPoint⁻¹ * b * G.longestPoint = u := by dsimp [b]; group
  rw [he] at hc
  have huN := (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one u).mp
    (opposite_unipotent_point G u hu) M
  have hn : IsNilpotent (Comodule.basePointsRepresentation
      (H := G.coordinateAlgebra) E u - 1) := by
    have h := huN.map (TensorProduct.lid K M).conjRingEquiv.toRingHom
    have hsub := map_sub (TensorProduct.lid K M).conjRingEquiv.toRingHom
      (Comodule.endOfPoint M u.ofConv) 1
    have hone := map_one (TensorProduct.lid K M).conjRingEquiv.toRingHom
    rw [hsub, hone] at h
    exact h
  have hcoef : (positiveDetFunctional G).comp
      (Comodule.basePointsRepresentation (H := G.coordinateAlgebra) E u) =
        c • positiveDetFunctional G := by
    apply LinearMap.ext
    intro x
    change positiveDetFunctional G
      (Comodule.basePointsRepresentation (H := G.coordinateAlgebra) E u x) = _
    rw [adjointExterior_points]
    exact LinearMap.congr_fun hc x
  have hc1 : c = 1 := functional_unipotent_scalar _ hn
    (positiveDetFunctional G) (positiveDetVector G) (positiveDet_pairing G) c hcoef
  simpa only [hc1, one_smul] using hc

/-- The regular coefficient is invariant under left translation by U minus. -/
theorem positiveDet_left_unipotent (u g : G.points) (hu : u ∈ G.oppositeUnipotentPoints) :
    (u * g).ofConv (positiveDetCoefficient G) = g.ofConv (positiveDetCoefficient G) := by
  let := adjointExteriorComodule G
  change (u * g).ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G)) =
    g.ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G))
  rw [Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient,
    map_mul, Module.End.mul_apply, adjointExterior_points]
  exact LinearMap.congr_fun (positiveDet_oppositeUnipotent G u hu) _

end SchubertGeometry.DeterminantSection
