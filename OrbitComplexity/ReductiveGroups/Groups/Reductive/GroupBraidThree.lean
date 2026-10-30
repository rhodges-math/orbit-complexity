import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAdjointStrings
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupA2Tangents
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaConjugateTangent
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaTangentDeterminesMorphism

/-! # Rank-two braid identities from conjugated additive subgroups -/

noncomputable section
namespace ReductiveGroups
open TauCeti
universe u
variable {K B : Type u} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

private theorem conjugate_points_eq (x y : B →ₐc[K] SymmetricAlgebra K K)
    (a b : WithConv (B →ₐ[K] K))
    (h : affineGroupAdjointLieEquiv a (gaAffineGroupTangent x) =
      affineGroupAdjointLieEquiv b (gaAffineGroupTangent y)) (t : K) :
    a * gaAffineGroupPoints x (Multiplicative.ofAdd t) * a⁻¹ =
      b * gaAffineGroupPoints y (Multiplicative.ofAdd t) * b⁻¹ := by
  have hm : x.comp (affineGroupConjugationBialgHom a) =
      y.comp (affineGroupConjugationBialgHom b) := by
    apply gaMorphism_ext_of_tangent_eq
    rw [gaTangent_comp_conjugation, gaTangent_comp_conjugation]
    exact h
  rw [← gaPoints_comp_conjugation, ← gaPoints_comp_conjugation, hm]

private theorem braid_of_conjugate_tangents
    (x y z w : B →ₐc[K] SymmetricAlgebra K K)
    (a b : WithConv (B →ₐ[K] K))
    (ha : a = gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
      gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)))
    (hb : b = gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K)) *
      gaAffineGroupPoints w (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K)))
    (he : affineGroupAdjointLieEquiv a (gaAffineGroupTangent z) =
      affineGroupAdjointLieEquiv b⁻¹ (gaAffineGroupTangent x))
    (hf : affineGroupAdjointLieEquiv a (gaAffineGroupTangent w) =
      affineGroupAdjointLieEquiv b⁻¹ (gaAffineGroupTangent y)) :
    a * b * a = b * a * b := by
  have hp := conjugate_points_eq z x a b⁻¹ he 1
  have hn := conjugate_points_eq w y a b⁻¹ hf (-1)
  simp only [inv_inv] at hp hn
  have hc : a * b * a⁻¹ = b⁻¹ * a * b := by
    calc
      a * b * a⁻¹ =
          (a * gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K)) * a⁻¹) *
          (a * gaAffineGroupPoints w (Multiplicative.ofAdd (-1 : K)) * a⁻¹) *
          (a * gaAffineGroupPoints z (Multiplicative.ofAdd (1 : K)) * a⁻¹) := by
            rw [hb]
            group
      _ = (b⁻¹ * gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) * b) *
          (b⁻¹ * gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) * b) *
          (b⁻¹ * gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) * b) := by
            rw [hp, hn]
      _ = b⁻¹ * a * b := by
        rw [ha]
        group
  calc
    a * b * a = b * (b⁻¹ * a * b) * a := by group
    _ = b * (a * b * a⁻¹) * a := by rw [hc]
    _ = b * a * b := by group

namespace ReductiveGroupData
variable [IsAlgClosed K] (G : ReductiveGroupData K)

private theorem reflectionPoint_inv_product (i : G.rootBase.support) :
    (G.reflectionPoint i.val)⁻¹ =
      gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (-1 : K)) *
      gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (1 : K)) *
      gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (-1 : K)) := by
  change (gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)) *
    gaAffineGroupPoints (G.negativeSimpleRootMap i) (Multiplicative.ofAdd (-1 : K)) *
    gaAffineGroupPoints (G.simpleRootMap i) (Multiplicative.ofAdd (1 : K)))⁻¹ = _
  have hpos : (Multiplicative.ofAdd (1 : K))⁻¹ = Multiplicative.ofAdd (-1 : K) := rfl
  have hneg : (Multiplicative.ofAdd (-1 : K))⁻¹ = Multiplicative.ofAdd (1 : K) :=
    congrArg Multiplicative.ofAdd (neg_neg (1 : K))
  simp only [mul_inv_rev, ← map_inv, hpos, hneg, ← mul_assoc]

/-- Fixed simple representatives satisfy the length-three braid in the full group. -/
theorem reflectionPoints_braid_three (i j : G.rootBase.support)
    (h : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem i.val *
      RootPairing.weylGroup.ofIdx G.rootSystem j.val) = 3) :
    G.reflectionPoint i.val * G.reflectionPoint j.val * G.reflectionPoint i.val =
      G.reflectionPoint j.val * G.reflectionPoint i.val * G.reflectionPoint j.val := by
  obtain ⟨⟨hfv, heev, hfev⟩, ⟨hew, hffw, hefw⟩⟩ := G.simple_root_a2_tangent_strings i j h
  have hrev : orderOf (RootPairing.weylGroup.ofIdx G.rootSystem j.val *
      RootPairing.weylGroup.ofIdx G.rootSystem i.val) = 3 := by
    calc
      _ = TauCeti.coxeterMatrixOfBase G.rootSystem G.rootBase j i :=
        RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
          G.rootSystem G.rootBase j i
      _ = TauCeti.coxeterMatrixOfBase G.rootSystem G.rootBase i j :=
        (TauCeti.coxeterMatrixOfBase G.rootSystem G.rootBase).symmetric j i
      _ = 3 := (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
        G.rootSystem G.rootBase i j).symm.trans h
  obtain ⟨⟨hfv', heev', hfev'⟩, ⟨hew', hffw', hefw'⟩⟩ :=
    G.simple_root_a2_tangent_strings j i hrev
  have hE := gaSl2Product_adjoint_lower (K := K) (B := G.coordinateAlgebra)
    (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    (gaAffineGroupTangent (G.simpleRootMap j)) 1 (one_mul 1) hfv heev hfev
  change affineGroupAdjointRepresentation (G.reflectionPoint i.val)
    (gaAffineGroupTangent (G.simpleRootMap j)) =
      (1 : K) • ⁅gaAffineGroupTangent (G.simpleRootMap i),
        gaAffineGroupTangent (G.simpleRootMap j)⁆ at hE
  have hE' := hE.trans (one_smul K _)
  have hF := gaSl2Product_adjoint_upper (K := K) (B := G.coordinateAlgebra)
    (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    (gaAffineGroupTangent (G.negativeSimpleRootMap j)) 1 (one_mul 1) hew hffw hefw
  change affineGroupAdjointRepresentation (G.reflectionPoint i.val)
    (gaAffineGroupTangent (G.negativeSimpleRootMap j)) =
      (-1 : K) • ⁅gaAffineGroupTangent (G.negativeSimpleRootMap i),
        gaAffineGroupTangent (G.negativeSimpleRootMap j)⁆ at hF
  have hF' := hF.trans (neg_one_smul K _)
  have hEinv : affineGroupAdjointRepresentation (G.reflectionPoint j.val)⁻¹
      (gaAffineGroupTangent (G.simpleRootMap i)) =
      (-1 : K) • ⁅gaAffineGroupTangent (G.simpleRootMap j),
        gaAffineGroupTangent (G.simpleRootMap i)⁆ := by
    simpa only [neg_neg, ← reflectionPoint_inv_product G j] using
      (gaSl2Product_adjoint_lower (K := K) (B := G.coordinateAlgebra)
        (G.simpleRootMap j) (G.negativeSimpleRootMap j)
        (gaAffineGroupTangent (G.simpleRootMap i)) (-1) (by ring) hfv' heev' hfev')
  have hEinv' := hEinv.trans ((neg_one_smul K _).trans (lie_skew _ _))
  have hFinv : affineGroupAdjointRepresentation (G.reflectionPoint j.val)⁻¹
      (gaAffineGroupTangent (G.negativeSimpleRootMap i)) =
      (1 : K) • ⁅gaAffineGroupTangent (G.negativeSimpleRootMap j),
        gaAffineGroupTangent (G.negativeSimpleRootMap i)⁆ := by
    simpa only [neg_neg, ← reflectionPoint_inv_product G j] using
      (gaSl2Product_adjoint_upper (K := K) (B := G.coordinateAlgebra)
        (G.simpleRootMap j) (G.negativeSimpleRootMap j)
        (gaAffineGroupTangent (G.negativeSimpleRootMap i)) (-1) (by ring) hew' hffw' hefw')
  have hFinv' := hFinv.trans ((one_smul K _).trans (lie_skew _ _).symm)
  apply braid_of_conjugate_tangents (K := K) (B := G.coordinateAlgebra)
    (G.simpleRootMap i) (G.negativeSimpleRootMap i)
    (G.simpleRootMap j) (G.negativeSimpleRootMap j)
    (G.reflectionPoint i.val) (G.reflectionPoint j.val) rfl rfl
  · exact hE'.trans hEinv'.symm
  · exact hF'.trans hFinv'.symm

end ReductiveGroupData

end ReductiveGroups
