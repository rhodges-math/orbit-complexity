import OrbitComplexity.GroupActions.Varieties.AffineMultiplication
import OrbitComplexity.GroupActions.Varieties.AffineTranslations
import OrbitComplexity.GroupActions.Varieties.PointDerivationSquares
import Mathlib.RingTheory.FiniteStability

/-!
# Multiplication and translation coordinates

Left translation in one factor and right translation in the other intertwine with
restricted affine multiplication. This transports bijectivity of its identity differential
to every rational point of the affine product.

## Main results

* `GroupActions.affineMulMap_translation`: the commuting coordinate square.
* `GroupActions.affineMulMap_deriv_bijective`: propagation of differential bijectivity.
-/

open scoped TensorProduct
namespace GroupActions
noncomputable section
universe u
private theorem tensorPoints_comp_map {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (p : (A →ₐ[K] K) × (B →ₐ[K] K))
    (f : A →ₐ[K] A) (g : B →ₐ[K] B) :
    ((tensorAlgebraPointsEquiv K A B).symm p).comp (Algebra.TensorProduct.map f g) =
      (tensorAlgebraPointsEquiv K A B).symm (p.1.comp f, p.2.comp g) := by
  ext <;> simp [tensorAlgebraPointsEquiv]

private theorem counit_tensor_points {K A B : Type u}
    [CommRing K] [CommRing A] [Bialgebra K A] [CommRing B] [Bialgebra K B] :
    Bialgebra.counitAlgHom K (A ⊗[K] B) =
      (tensorAlgebraPointsEquiv K A B).symm
        (Bialgebra.counitAlgHom K A, Bialgebra.counitAlgHom K B) := by
  ext <;> simp [tensorAlgebraPointsEquiv, Bialgebra.counitAlgHom]

variable {K H A B : Type u} [Field K] [IsAlgClosed K]
  [CommRing H] [HopfAlgebra K H] [Algebra.FiniteType K H] [IsReduced H]
  [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] [IsReduced A]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]
  [IsReduced (A ⊗[K] B)]

/-- Coordinate translations intertwine restricted multiplication. -/
theorem affineMulMap_translation (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (a : WithConv (A →ₐ[K] K)) (b : WithConv (B →ₐ[K] K)) :
    (Algebra.TensorProduct.map (leftTranslationAlgEquiv a).toAlgHom
      (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b).toAlgHom).comp
        (affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B)) =
      (affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B)).comp
        (((leftTranslationAlgEquiv (WithConv.toConv (a.ofConv.comp f))).trans
          (TauCeti.HopfAlgebra.rightTranslationAlgEquiv
            (WithConv.toConv (b.ofConv.comp g)))).toAlgHom) := by
  let : Algebra.FiniteType K (A ⊗[K] B) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A)
      (inferInstance : Algebra.FiniteType A (A ⊗[K] B))
  ext h
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := K) (K := K)
  intro q
  obtain ⟨p, rfl⟩ := (tensorAlgebraPointsEquiv K A B).symm.surjective q
  have hp : ((tensorAlgebraPointsEquiv K A B).symm p).comp
      ((Algebra.TensorProduct.map (leftTranslationAlgEquiv a).toAlgHom
        (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b).toAlgHom).comp
          (affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B))) =
      ((tensorAlgebraPointsEquiv K A B).symm p).comp
        ((affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B)).comp
          (((leftTranslationAlgEquiv (WithConv.toConv (a.ofConv.comp f))).trans
            (TauCeti.HopfAlgebra.rightTranslationAlgEquiv
              (WithConv.toConv (b.ofConv.comp g)))).toAlgHom)) := by
    rw [← AlgHom.comp_assoc, tensorPoints_comp_map, affineMulMap_points,
      leftTranslationAlgEquiv_toAlgHom, TauCeti.HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
    apply WithConv.toConv_injective
    change WithConv.toConv
        (((WithConv.toConv ((p.1.comp (ReductiveGroups.leftTranslationAlgHom a)).comp
            (f : H →ₐ[K] A))) *
          (WithConv.toConv ((p.2.comp (TauCeti.HopfAlgebra.rightTranslationAlgHom b)).comp
            (g : H →ₐ[K] B)))).ofConv) = _
    have hL := congrArg WithConv.ofConv
      (ReductiveGroups.toConv_comp_leftTranslationAlgHom (WithConv.toConv p.1) a)
    have hR := congrArg WithConv.ofConv
      (TauCeti.HopfAlgebra.toConv_comp_rightTranslationAlgHom (WithConv.toConv p.2) b)
    change p.1.comp (ReductiveGroups.leftTranslationAlgHom a) =
      (a * WithConv.toConv p.1).ofConv at hL
    change p.2.comp (TauCeti.HopfAlgebra.rightTranslationAlgHom b) =
      (WithConv.toConv p.2 * b).ofConv at hR
    rw [hL, hR, AlgHom.convMul_comp_bialgHom_distrib,
      AlgHom.convMul_comp_bialgHom_distrib]
    change _ = WithConv.toConv
      (((((tensorAlgebraPointsEquiv K A B).symm p).comp
        (affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B))).comp
          (TauCeti.HopfAlgebra.rightTranslationAlgHom (WithConv.toConv (b.ofConv.comp g)))).comp
            (ReductiveGroups.leftTranslationAlgHom (WithConv.toConv (a.ofConv.comp f))))
    rw [affineMulMap_points, ReductiveGroups.toConv_comp_leftTranslationAlgHom,
      TauCeti.HopfAlgebra.toConv_comp_rightTranslationAlgHom]
    simp only [WithConv.toConv_ofConv]
    simp only [mul_assoc]
  exact AlgHom.congr_fun hp h

/-- Bijectivity of a restricted multiplication derivative propagates from the identity. -/
theorem affineMulMap_deriv_bijective (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (h : Function.Bijective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
      (Bialgebra.counitAlgHom K (A ⊗[K] B)))) (q : A ⊗[K] B →ₐ[K] K) :
    Function.Bijective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom) q) := by
  let p := tensorAlgebraPointsEquiv K A B q
  let a := WithConv.toConv p.1
  let b := WithConv.toConv p.2
  let eT := Algebra.TensorProduct.congr (leftTranslationAlgEquiv a)
    (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b)
  let eS := (leftTranslationAlgEquiv (WithConv.toConv (a.ofConv.comp f.toAlgHom))).trans
    (TauCeti.HopfAlgebra.rightTranslationAlgEquiv (WithConv.toConv (b.ofConv.comp g.toAlgHom)))
  have hcomm : eT.toAlgHom.comp (affineMulMap f.toAlgHom g.toAlgHom) =
      (affineMulMap f.toAlgHom g.toAlgHom).comp eS.toAlgHom :=
    affineMulMap_translation f g a b
  have hpoint : (Bialgebra.counitAlgHom K (A ⊗[K] B)).comp eT.toAlgHom = q := by
    rw [counit_tensor_points]
    change ((tensorAlgebraPointsEquiv K A B).symm
      (Bialgebra.counitAlgHom K A, Bialgebra.counitAlgHom K B)).comp
        (Algebra.TensorProduct.map (leftTranslationAlgEquiv a).toAlgHom
          (TauCeti.HopfAlgebra.rightTranslationAlgEquiv b).toAlgHom) = q
    rw [tensorPoints_comp_map, leftTranslationAlgEquiv_toAlgHom,
      TauCeti.HopfAlgebra.rightTranslationAlgEquiv_toAlgHom,
      counit_comp_leftTranslation, TauCeti.HopfAlgebra.counitAlgHom_comp_rightTranslationAlgHom]
    exact (tensorAlgebraPointsEquiv K A B).symm_apply_apply q
  have htranslated := (bijective_pointPrecomp_equiv (affineMulMap f.toAlgHom g.toAlgHom)
    eS eT hcomm (Bialgebra.counitAlgHom K (A ⊗[K] B))).mp h
  erw [hpoint] at htranslated
  exact htranslated
end
end GroupActions
