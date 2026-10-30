import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.HighestCoefficient
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Power
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # The regular rightmost-frame reset and its fixed integer powers -/

open ReductiveGroups TauCeti GroupActions WithConv
noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev E := ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact isReduced_of_smooth K G.coordinateAlgebra

attribute [local instance] coordinateReduced

private def universalPoint :
    WithConv (G.coordinateAlgebra →ₐ[K] Polynomial G.coordinateAlgebra) :=
  toConv (Polynomial.CAlgHom (R := K) (A := G.coordinateAlgebra))

private def constantPoint (g : G.points) :
    WithConv (G.coordinateAlgebra →ₐ[K] Polynomial G.coordinateAlgebra) :=
  AlgHom.mapValue (Algebra.ofId K (Polynomial G.coordinateAlgebra)) g

/-- Pullback by the regular family (g,T) mapping to g*x_i(T)*n_i inverse,
written as a polynomial over the original group coordinate ring. -/
def simpleFramePolynomial (i : G.rootBase.support) :
    G.coordinateAlgebra →ₐ[K] Polynomial G.coordinateAlgebra :=
  (universalPoint G * gaParameterPoint (G.simpleRootMap i) Polynomial.X *
    constantPoint G (G.reflectionPoint i.val)⁻¹).ofConv

private theorem family_eval (i : G.rootBase.support)
    (g : G.coordinateAlgebra →ₐ[K] K) (t : K) (f : G.coordinateAlgebra) :
    ((simpleFramePolynomial G i f).map g.toRingHom).eval t =
      (toConv g * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹).ofConv f := by
  let s : Polynomial G.coordinateAlgebra →ₐ[K] K :=
    (Polynomial.aeval t).comp (Polynomial.mapAlgHom g)
  have h1 : AlgHom.mapValue s (universalPoint G) = toConv g := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    simp [universalPoint, s, AlgHom.mapValue_apply]
  have h2 : AlgHom.mapValue s (gaParameterPoint (G.simpleRootMap i)
      (Polynomial.X : Polynomial G.coordinateAlgebra)) =
        gaParameterPoint (G.simpleRootMap i) t := by
    have h := gaParameterPoint_mapValue (G.simpleRootMap i) s Polynomial.X
    simpa only [s, AlgHom.comp_apply, Polynomial.coe_mapAlgHom, Polynomial.map_X,
      Polynomial.aeval_X] using h
  have h3 : AlgHom.mapValue s (constantPoint G (G.reflectionPoint i.val)⁻¹) =
      (G.reflectionPoint i.val)⁻¹ := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    change s (algebraMap K (Polynomial G.coordinateAlgebra)
      (((G.reflectionPoint i.val)⁻¹).ofConv x)) = _
    exact s.commutes _
  have he : AlgHom.mapValue s
      (universalPoint G * gaParameterPoint (G.simpleRootMap i) Polynomial.X *
        constantPoint G (G.reflectionPoint i.val)⁻¹) =
      toConv g * gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹ := by
    rw [map_mul, map_mul, h1, h2, h3]
  exact congrArg (fun p => p.ofConv f) he

private def scalarFrame (i : G.rootBase.support) (g : G.points) : Polynomial K :=
  letI := adjointExteriorComodule G
  let rho := Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G)
  gaPolynomialEquiv K (G.simpleRootMap i
    (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      ((positiveDetFunctional G).comp (rho g))
      (rho (G.reflectionPoint i.val)⁻¹ (positiveDetVector G))))

omit [IsAlgClosed K] [CharZero K] in
private theorem matrix_frame_eval {H V : Type*} [CommRing H] [HopfAlgebra K H]
    [AddCommGroup V] [Module K V] [Comodule K H V]
    (g x r : WithConv (H →ₐ[K] K)) (phi : V →ₗ[K] K) (v : V) :
    x.ofConv (Comodule.matrixCoefficient (R := K) (C := H)
      (phi.comp (Comodule.basePointsRepresentation (R := K) (H := H) V g))
      (Comodule.basePointsRepresentation (R := K) (H := H) V r v)) =
    (g * x * r).ofConv (Comodule.matrixCoefficient (R := K) (C := H) phi v) := by
  rw [Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient]
  simp only [map_mul, Module.End.mul_apply, LinearMap.comp_apply]

private theorem scalarFrame_eval (i : G.rootBase.support) (g : G.points) (t : K) :
    (scalarFrame G i g).eval t =
      (g * gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹).ofConv
        (positiveDetCoefficient G) := by
  let := adjointExteriorComodule G
  rw [scalarFrame, gaPolynomialEquiv_eval_point]
  exact matrix_frame_eval (K := K) (H := G.coordinateAlgebra)
    (V := E G) g (gaParameterPoint (G.simpleRootMap i) t)
    (G.reflectionPoint i.val)⁻¹ (positiveDetFunctional G) (positiveDetVector G)

private theorem family_specialize (i : G.rootBase.support)
    (g : G.coordinateAlgebra →ₐ[K] K) :
    (simpleFramePolynomial G i (positiveDetCoefficient G)).map g.toRingHom =
      scalarFrame G i (toConv g) := by
  apply Polynomial.funext
  intro t
  rw [family_eval, scalarFrame_eval]

private theorem scalarFrame_coefficient (i : G.rootBase.support) (g : G.points) (n : ℕ) :
    (scalarFrame G i g).coeff n =
      letI := adjointExteriorComodule G
      positiveDetFunctional G
        (Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G) g
          (simpleFrameCoefficient G i n)) := by
  let := adjointExteriorComodule G
  exact (simpleFrameCoefficient_apply G i n ((positiveDetFunctional G).comp
    (Comodule.basePointsRepresentation (R := K) (H := G.coordinateAlgebra) (E G) g))).symm

/-- Every coefficient of the regular rightmost-frame pullback is the corresponding
matrix coefficient of the framed exterior vector. -/
theorem simpleFrame_coefficient (i : G.rootBase.support) (n : ℕ) :
    (simpleFramePolynomial G i (positiveDetCoefficient G)).coeff n =
      letI := adjointExteriorComodule G
      Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (simpleFrameCoefficient G i n) := by
  let := adjointExteriorComodule G
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K) (A := G.coordinateAlgebra)
  intro g
  calc
    g ((simpleFramePolynomial G i (positiveDetCoefficient G)).coeff n) =
        ((simpleFramePolynomial G i (positiveDetCoefficient G)).map g.toRingHom).coeff n :=
      (Polynomial.coeff_map (p := simpleFramePolynomial G i (positiveDetCoefficient G))
        g.toRingHom n).symm
    _ = (scalarFrame G i (toConv g)).coeff n :=
      congrArg (fun p : Polynomial K => p.coeff n) (family_specialize G i g)
    _ = _ := by rw [scalarFrame_coefficient, Comodule.apply_matrixCoefficient]

/-- The unpowered regular frame polynomial has degree at most two, before
any coefficient model or residue prime is chosen. -/
theorem simpleFrame_degree (i : G.rootBase.support) :
    (simpleFramePolynomial G i (positiveDetCoefficient G)).natDegree ≤ 2 := by
  let := adjointExteriorComodule G
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [simpleFrame_coefficient, simpleFrameCoefficient_zero G i n hn,
    Comodule.matrixCoefficient_zero]

/-- The unpowered top coefficient is the original full-character determinant. -/
theorem simpleFrame_top (i : G.rootBase.support) :
    (simpleFramePolynomial G i (positiveDetCoefficient G)).coeff 2 =
      positiveDetCoefficient G := by
  let := adjointExteriorComodule G
  rw [simpleFrame_coefficient, simpleFrameCoefficient_top]
  rfl

/-- The rightmost append has top coefficient F to the same fixed integer power.
The coefficient ring and exponent are chosen before any residue prime. -/
theorem simpleFrame_power_top (i : G.rootBase.support) (N : ℕ) :
    (simpleFramePolynomial G i (positiveDetPower G N)).coeff (2 * N) =
      positiveDetPower G N := by
  change (simpleFramePolynomial G i (positiveDetCoefficient G ^ N)).coeff (2 * N) =
    positiveDetCoefficient G ^ N
  rw [map_pow]
  have h := Polynomial.coeff_pow_of_natDegree_le
    (m := N) (simpleFrame_degree G i)
  simpa only [Nat.mul_comm, simpleFrame_top] using h

end SchubertGeometry.DeterminantSection
