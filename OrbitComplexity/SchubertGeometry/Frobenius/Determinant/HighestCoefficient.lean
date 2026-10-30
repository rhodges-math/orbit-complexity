import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.GaussPolynomial
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.ExteriorWeights
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterReflection
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaCoefficientConvolution
import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Full torus weights of the rightmost simple-frame coefficients -/

open ReductiveGroups TauCeti GroupActions
open SchubertGeometry.ProjectiveLine
open scoped TensorProduct
noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact isReduced_of_smooth K G.coordinateAlgebra

attribute [local instance] coordinateReduced
private abbrev E := ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent

private def frameVector (i : G.rootBase.support) : E G :=
  letI := adjointExteriorComodule G
  Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
    (G.reflectionPoint i.val)⁻¹ (positiveDetVector G)

/-- The coefficient vector of rho(x_i(T)n_i inverse) applied to the
positive determinant vector. The coordinate is the rightmost appended factor. -/
def simpleFrameCoefficient (i : G.rootBase.support) (n : ℕ) :
    ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent :=
  letI := adjointExteriorComodule G
  LinearMap.tensorComponent
    ((gaCoefficientLinear K n).comp (G.simpleRootMap i).toLinearMap)
      (Comodule.coact (R := K) (C := G.coordinateAlgebra) (M := E G) (frameVector G i))

private def framePolynomial (i : G.rootBase.support) (phi : E G →ₗ[K] K) : Polynomial K :=
  letI := adjointExteriorComodule G
  gaPolynomialEquiv K (G.simpleRootMap i
    (Comodule.matrixCoefficient (C := G.coordinateAlgebra) phi (frameVector G i)))

private theorem coefficient_apply (i : G.rootBase.support) (n : ℕ)
    (phi : E G →ₗ[K] K) :
    phi (simpleFrameCoefficient G i n) = (framePolynomial G i phi).coeff n := by
  let := adjointExteriorComodule G
  change phi (LinearMap.tensorComponent
      ((gaCoefficientLinear K n).comp (G.simpleRootMap i).toLinearMap)
      (Comodule.coact (R := K) (C := G.coordinateAlgebra) (M := E G) (frameVector G i))) =
    gaCoefficientLinear K n (G.simpleRootMap i
      (TensorProduct.lid K G.coordinateAlgebra
        (TensorProduct.map phi LinearMap.id
          (Comodule.coact (R := K) (C := G.coordinateAlgebra) (M := E G)
            (frameVector G i)))))
  generalize Comodule.coact (R := K) (C := G.coordinateAlgebra) (M := E G)
    (frameVector G i) = x
  induction x using TensorProduct.inductionOn with
  | tmul v c =>
    simp only [LinearMap.tensorComponent_tmul, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
      map_smul, smul_eq_mul]
    exact mul_comm _ _
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Testing the framed coefficient vector by any functional is ordinary
polynomial coefficient extraction on the matrix coefficient. -/
theorem simpleFrameCoefficient_apply (i : G.rootBase.support) (n : ℕ)
    (phi : (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent) →ₗ[K] K) :
    phi (simpleFrameCoefficient G i n) =
      letI := adjointExteriorComodule G
      gaCoefficientLinear K n (G.simpleRootMap i
        (Comodule.matrixCoefficient (C := G.coordinateAlgebra) phi
          (Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra)
            (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
            (G.reflectionPoint i.val)⁻¹ (positiveDetVector G)))) := by
  exact coefficient_apply G i n phi
private theorem polynomial_eval (i : G.rootBase.support) (phi : E G →ₗ[K] K) (a : K) :
    (framePolynomial G i phi).eval a =
      letI := adjointExteriorComodule G
      phi (Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
        (gaParameterPoint (G.simpleRootMap i) a) (frameVector G i)) := by
  let := adjointExteriorComodule G
  rw [framePolynomial, gaPolynomialEquiv_eval_point]
  change (gaParameterPoint (G.simpleRootMap i) a).ofConv
    (Comodule.matrixCoefficient (C := G.coordinateAlgebra) phi (frameVector G i)) = _
  exact Comodule.apply_matrixCoefficient _ _ _

omit [IsAlgClosed K] [CharZero K] in
private theorem representation_frame {R P V : Type*} [CommRing R] [Monoid P]
    [AddCommGroup V] [Module R V] (rho : P →* Module.End R V)
    (t x y r q : P) (v : V) (s : R)
    (hg : t * x * r = y * r * q) (hw : rho q v = s • v) :
    rho t (rho x (rho r v)) = s • rho y (rho r v) := by
  have h := congrArg (fun g : P => rho g v) hg
  simpa only [map_mul, Module.End.mul_apply, hw, map_smul] using h

private theorem torus_frame (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) (a : K) :
    letI := adjointExteriorComodule G
    let rho := Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
    let c := DiagonalizableGroup.pointsMulEquiv z (G.rootCharacter i.val)
    let d := DiagonalizableGroup.pointsMulEquiv z G.positiveRootCharacter
    rho (AlgHom.mapDomain G.torusSplit z)
        (rho (gaParameterPoint (G.simpleRootMap i) a) (frameVector G i)) =
      (↑(d * c ^ (-2 : ℤ)) : K) •
        rho (gaParameterPoint (G.simpleRootMap i) ((c : K) * a)) (frameVector G i) := by
  let := adjointExteriorComodule G
  let rho := Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
  let n := G.reflectionPoint i.val
  let t := AlgHom.mapDomain G.torusSplit z
  let zz : WithConv (MonoidAlgebra K G.characters →ₐ[K] K) :=
    AlgHom.mapDomain (reflectionTorusMap G i) z
  let tt := AlgHom.mapDomain G.torusSplit zz
  let c := DiagonalizableGroup.pointsMulEquiv z (G.rootCharacter i.val)
  let d := DiagonalizableGroup.pointsMulEquiv z G.positiveRootCharacter
  have ht := simpleReflection_torus_points G i z
  change tt = n * t * n⁻¹ at ht
  have he : G.oddRootCharacter 3 = G.positiveRootCharacter := by
    simp only [ReductiveGroupData.oddRootCharacter, Nat.reduceSub, Nat.reduceDiv, pow_one]
  have hd := simpleReflection_odd_eval G 3 (by decide) i z
  rw [he] at hd
  change DiagonalizableGroup.pointsMulEquiv zz G.positiveRootCharacter =
    d * c ^ (-2 : ℤ) at hd
  have hw : rho tt (positiveDetVector G) =
      (↑(d * c ^ (-2 : ℤ)) : K) • positiveDetVector G := by
    have h := positiveDet_torus G zz
    change rho tt (positiveDetVector G) =
      (↑(DiagonalizableGroup.pointsMulEquiv zz G.positiveRootCharacter) : K) •
        positiveDetVector G at h
    rwa [hd] at h
  have hx := GaAffineGroupPoints.conjugate_of_character_weight G.torusSplit
    (G.rootCharacter i.val) z (G.simpleRootMap i) (G.simpleRootMap_tangent_mem i) a
  change t * gaParameterPoint (G.simpleRootMap i) a * t⁻¹ =
    gaParameterPoint (G.simpleRootMap i) ((c : K) * a) at hx
  have hg : t * gaParameterPoint (G.simpleRootMap i) a * n⁻¹ =
      gaParameterPoint (G.simpleRootMap i) ((c : K) * a) * n⁻¹ * tt := by
    rw [ht, ← hx]
    group
  exact representation_frame (R := K) rho t
    (gaParameterPoint (G.simpleRootMap i) a)
    (gaParameterPoint (G.simpleRootMap i) ((c : K) * a)) n⁻¹ tt
    (positiveDetVector G) (↑(d * c ^ (-2 : ℤ)) : K) hg hw

private theorem coefficient_torus (i : G.rootBase.support) (n : ℕ)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    letI := adjointExteriorComodule G
    Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
        (AlgHom.mapDomain G.torusSplit z) (simpleFrameCoefficient G i n) =
      z.ofConv (MonoidAlgebra.single
        (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2)) 1) •
          simpleFrameCoefficient G i n := by
  let := adjointExteriorComodule G
  let rho := Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
  let t := AlgHom.mapDomain G.torusSplit z
  let c := DiagonalizableGroup.pointsMulEquiv z (G.rootCharacter i.val)
  let d := DiagonalizableGroup.pointsMulEquiv z G.positiveRootCharacter
  let s : K := ↑(d * c ^ (-2 : ℤ))
  have hp (phi : E G →ₗ[K] K) :
      framePolynomial G i (phi.comp (rho t)) =
        s • (framePolynomial G i phi).comp (Polynomial.C (c : K) * Polynomial.X) := by
    apply Polynomial.funext
    intro a
    simp only [Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [polynomial_eval, polynomial_eval]
    change phi (rho t (rho (gaParameterPoint (G.simpleRootMap i) a)
      (frameVector G i))) = _
    rw [torus_frame G i z a, map_smul]
  have hs : s * (c : K) ^ n =
      z.ofConv (MonoidAlgebra.single
        (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2)) 1) := by
    have hu : (d * c ^ (-2 : ℤ)) * c ^ n = d * c ^ ((n : ℤ) - 2) := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add]
      congr 1
    change (↑(d * c ^ (-2 : ℤ)) : K) * (c : K) ^ n =
      (↑(DiagonalizableGroup.pointsMulEquiv z
        (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2))) : K)
    rw [map_mul, map_zpow]
    exact congrArg (fun x : Kˣ => (x : K)) hu
  apply (Module.finBasis K (E G)).repr.injective
  apply Finsupp.ext
  intro j
  let phi := (Module.finBasis K (E G)).coord j
  have h := congrArg (fun p : Polynomial K => p.coeff n) (hp phi)
  rw [Polynomial.coeff_smul, Polynomial.comp_C_mul_X_coeff] at h
  change (framePolynomial G i (phi.comp (rho t))).coeff n =
    s * ((framePolynomial G i phi).coeff n * (c : K) ^ n) at h
  have hc : phi (rho t (simpleFrameCoefficient G i n)) =
      s * (c : K) ^ n * phi (simpleFrameCoefficient G i n) := by
    calc
      _ = (framePolynomial G i (phi.comp (rho t))).coeff n :=
        coefficient_apply G i n (phi.comp (rho t))
      _ = _ := by rw [h, ← coefficient_apply G i n phi]; ring
  change phi (rho t (simpleFrameCoefficient G i n)) =
    phi (z.ofConv (MonoidAlgebra.single
      (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2)) 1) •
        simpleFrameCoefficient G i n)
  rw [map_smul, smul_eq_mul, ← hs]
  exact hc

omit [IsAlgClosed K] [CharZero K] in
private theorem point_contraction {H V X : Type*} [CommRing H] [HopfAlgebra K H]
    [AddCommGroup V] [Module K V] [Comodule K H V] [Monoid X]
    (pi : H →ₐc[K] MonoidAlgebra K X) (z : MonoidAlgebra K X →ₐ[K] K) (v : V) :
    TensorProduct.lid K V
        (TensorProduct.map z.toLinearMap (LinearMap.id : V →ₗ[K] V)
          (TensorProduct.comm K V (MonoidAlgebra K X)
            (TensorProduct.map (LinearMap.id : V →ₗ[K] V) pi.toCoalgHom.toLinearMap
              (Comodule.coact (R := K) (C := H) (M := V) v)))) =
      Comodule.basePointsRepresentation (R := K) (H := H) V
        (AlgHom.mapDomain pi (WithConv.toConv z)) v := by
  rw [Comodule.basePointsRepresentation_apply, AlgHom.mapDomain_apply]
  change _ = TensorProduct.lid K V
    (Comodule.endOfPoint V (z.comp pi.toAlgHom) (1 ⊗ₜ[K] v))
  rw [DiagonalizableGroup.endOfPoint_tmul_comp, one_smul,
    LinearMap.lTensor_def, TensorProduct.map_comm]
  rfl

private theorem weight_of_points (chi : G.characters) (v : E G)
    (hv : letI := adjointExteriorComodule G
      ∀ z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K),
        Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
          (AlgHom.mapDomain G.torusSplit z) v =
            z.ofConv (MonoidAlgebra.single chi 1) • v) :
    letI := adjointExteriorComodule G
    v ∈ DiagonalizableGroup.weightSpace (E G) G.torusSplit.toCoalgHom chi := by
  let := adjointExteriorComodule G
  let : Algebra.FiniteType K (MonoidAlgebra K G.characters) :=
    Algebra.FiniteType.of_surjective G.torusSplit.toAlgHom G.split_surjective
  apply DiagonalizableGroup.mem_weightSpace.mpr
  apply (TensorProduct.comm K (E G) (MonoidAlgebra K G.characters)).injective
  apply TauCeti.tensor_eq_of_forall_map_algHom_eq (K := K)
  intro z
  apply (TensorProduct.lid K (E G)).injective
  have hp := point_contraction (K := K) (V := E G) G.torusSplit z v
  calc
    _ = Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
        (AlgHom.mapDomain G.torusSplit (WithConv.toConv z)) v := hp
    _ = z (MonoidAlgebra.single chi 1) • v := hv (WithConv.toConv z)
    _ = _ := by
      simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.lid_tmul]
      rfl

/-- Every rightmost-frame coefficient has its full shifted torus character. -/
theorem simpleFrameCoefficient_weight (i : G.rootBase.support) (n : ℕ) :
    letI := adjointExteriorComodule G
    simpleFrameCoefficient G i n ∈
      DiagonalizableGroup.weightSpace
        (⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent)
        G.torusSplit.toCoalgHom
        (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2)) := by
  exact weight_of_points G _ _ (coefficient_torus G i n)

/-- Coefficients above degree two vanish in the framed exterior representation. -/
theorem simpleFrameCoefficient_zero (i : G.rootBase.support) (n : ℕ) (hn : 2 < n) :
    simpleFrameCoefficient G i n = 0 := by
  let := adjointExteriorComodule G
  by_contra hv
  have hocc : DiagonalizableGroup.weightSpace (E G) G.torusSplit.toCoalgHom
      (G.positiveRootCharacter * G.rootCharacter i.val ^ ((n : ℤ) - 2)) ≠ ⊥ := by
    intro hbot
    have hm := simpleFrameCoefficient_weight G i n
    rw [hbot] at hm
    change simpleFrameCoefficient G i n = 0 at hm
    exact hv hm
  have h := DeterminantWeights.determinant_positive_simple_domination G i ((n : ℤ) - 2) hocc
  omega

/-- The leading coefficient vector is the original positive determinant vector,
with scalar fixed by the Gauss pullback X squared. -/
theorem simpleFrameCoefficient_top (i : G.rootBase.support) :
    simpleFrameCoefficient G i 2 = positiveDetVector G := by
  let := adjointExteriorComodule G
  have hw : simpleFrameCoefficient G i 2 ∈
      DiagonalizableGroup.weightSpace (E G) G.torusSplit.toCoalgHom
        G.positiveRootCharacter := by
    simpa only [Nat.cast_ofNat, sub_self, zpow_zero, mul_one] using
      simpleFrameCoefficient_weight G i 2
  rw [DeterminantWeights.determinant_positive_weight_line G] at hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have heval : positiveDetFunctional G (simpleFrameCoefficient G i 2) = 1 := by
    rw [coefficient_apply]
    have he : Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (frameVector G i) =
      HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
        (positiveDetCoefficient G) := by
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro g
      change (WithConv.toConv g).ofConv
        (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
          (positiveDetFunctional G) (frameVector G i)) =
        (WithConv.toConv g).ofConv
          (HopfAlgebra.rightTranslationAlgHom ((G.reflectionPoint i.val)⁻¹)
            (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
              (positiveDetFunctional G) (positiveDetVector G)))
      rw [HopfAlgebra.ofConv_rightTranslationAlgHom,
        Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient,
        map_mul, Module.End.mul_apply]
      rfl
    change (gaPolynomialEquiv K (G.simpleRootMap i
      (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (frameVector G i)))).coeff 2 = 1
    rw [he, positiveDet_simple_polynomial]
    simp
  have hc1 : c = 1 := by
    have h := congrArg (positiveDetFunctional G) hc
    simpa only [map_smul, positiveDet_pairing, smul_eq_mul, mul_one, heval] using h
  simpa only [hc1, one_smul] using hc.symm

end SchubertGeometry.DeterminantSection
