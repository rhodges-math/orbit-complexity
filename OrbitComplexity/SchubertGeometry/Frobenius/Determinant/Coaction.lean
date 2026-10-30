import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.BorelCharacter
import OrbitComplexity.GroupActions.Rosenlicht.TensorPoints

/-! # The regular right-character equation for the determinant section -/

open ReductiveGroups TauCeti GroupActions WithConv
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

omit [CharZero K] in
private theorem borelReduced : IsReduced G.borelAlgebra := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact isReduced_of_smooth K G.borelAlgebra

attribute [local instance] coordinateReduced borelReduced

/-- The coordinate restriction to B is the full positive-root character. -/
theorem positiveDet_borel_restriction :
    ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (positiveDetCoefficient
      G) =
      borelCharacterMap G G.positiveRootCharacter
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K) (A := G.borelAlgebra)
  intro b
  exact positiveDet_borel_character G (toConv b)

omit [IsAlgClosed K] [CharZero K] in
private theorem right_evaluation (g : G.coordinateAlgebra →ₐ[K] K)
    (b : G.borelAlgebra →ₐ[K] K) (x : G.coordinateAlgebra) :
    b (tensorPointEval g
      ((Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra)
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom).toAlgHom)
          (Bialgebra.comulAlgHom K G.coordinateAlgebra x))) =
      (toConv g * TauCeti.AlgHom.mapDomain
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (toConv b)).ofConv x
          := by
  let q : G.coordinateAlgebra →ₐ[K] G.borelAlgebra :=
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom.toAlgHom
  have he : (b.comp (tensorPointEval g)).toLinearMap.comp
      (Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra) q).toLinearMap =
      (LinearMap.mul' K K).comp (TensorProduct.map g.toLinearMap (b.comp q).toLinearMap) := by
    apply TensorProduct.ext'
    intro a c
    change b (g a • q c) = g a * (b.comp q) c
    rw [map_smul]
    rfl
  have hm : ((toConv g * TauCeti.AlgHom.mapDomain
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (toConv
          b)).ofConv).toLinearMap =
      (LinearMap.mul' K K).comp
        ((TensorProduct.map g.toLinearMap (b.comp q).toLinearMap).comp Coalgebra.comul) := by
    have h := AlgHom.toLinearMap_convMul (toConv g)
      (TauCeti.AlgHom.mapDomain
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (toConv b))
    rw [LinearMap.convMul_def] at h
    exact WithConv.toConv_injective h
  change ((b.comp (tensorPointEval g)).toLinearMap.comp
    (Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra) q).toLinearMap)
      (Coalgebra.comul x) = _
  rw [he]
  exact (LinearMap.congr_fun hm x).symm

/-- The constructed coefficient satisfies the regular Borel coaction equation. -/
theorem positiveDet_right_coaction :
    (Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra)
      ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom).toAlgHom)
        (Bialgebra.comulAlgHom K G.coordinateAlgebra (positiveDetCoefficient G)) =
      positiveDetCoefficient G ⊗ₜ[K]
        borelCharacterMap G G.positiveRootCharacter
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  apply tensorPointEval_jointlyInjective (A := G.coordinateAlgebra) (B := G.borelAlgebra)
  intro g
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K) (A := G.borelAlgebra)
  intro b
  refine (right_evaluation G g b (positiveDetCoefficient G)).trans ?_
  have hb : TauCeti.AlgHom.mapDomain
      ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (toConv b) ∈
        G.borelPoints := by
    exact ⟨toConv b, rfl⟩
  rw [positiveDet_right_borel G (toConv g) _ hb]
  have hc := positiveDet_borel_character G (toConv b)
  change (TauCeti.AlgHom.mapDomain
      ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom) (toConv b)).ofConv
      (positiveDetCoefficient G) = _ at hc
  rw [hc]
  change b (borelCharacterMap G G.positiveRootCharacter
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) * g (positiveDetCoefficient G) =
    b (g (positiveDetCoefficient G) • borelCharacterMap G G.positiveRootCharacter
      (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))
  rw [map_smul, smul_eq_mul, mul_comm]

end SchubertGeometry.DeterminantSection
