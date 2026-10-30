import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRadicalCharacteristic
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointFirstOrder
import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Affine Group Conjugation Morphism

Conjugation by one field-valued point as a coordinate map. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv
open scoped TensorProduct

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

private def scalarPoint (g : WithConv (B →ₐ[K] K)) : WithConv (B →ₐ[K] B) :=
  toConv ((IsScalarTower.toAlgHom K K B).comp g.ofConv)

/-- Evaluation of the universal conjugation coordinate morphism at the
fixed field-valued point in its first tensor factor. -/
def affineGroupConjugationAlgHom (g : WithConv (B →ₐ[K] K)) : B →ₐ[K] B :=
  (Algebra.TensorProduct.productMap (scalarPoint g).ofConv (AlgHom.id K B)).comp
    (TauCeti.HopfAlgebra.conjugationAlgHom (R := K) (H := B))

private theorem affineGroupConjugationAlgHom_conv (g : WithConv (B →ₐ[K] K)) :
    toConv (affineGroupConjugationAlgHom g) =
      scalarPoint g * toConv (AlgHom.id K B) * (scalarPoint g)⁻¹ := by
  rw [affineGroupConjugationAlgHom,
    TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom]

/-- The fixed coordinate map acts on every algebra-valued point by the
ordinary group-theoretic conjugation of that point. -/
theorem affineGroupConjugationAlgHom_point
    {A : Type*} [CommRing A] [Algebra K A]
    (g : WithConv (B →ₐ[K] K)) (x : WithConv (B →ₐ[K] A)) :
    toConv (x.ofConv.comp (affineGroupConjugationAlgHom g)) =
      toConv ((IsScalarTower.toAlgHom K K A).comp g.ofConv) * x *
        (toConv ((IsScalarTower.toAlgHom K K A).comp g.ofConv))⁻¹ := by
  change (AlgHom.mapValue (H := B) x.ofConv)
    (toConv (affineGroupConjugationAlgHom g)) = _
  rw [affineGroupConjugationAlgHom_conv, map_mul, map_mul, map_inv]
  have hs : x.ofConv.comp ((IsScalarTower.toAlgHom K K B).comp g.ofConv) =
      (IsScalarTower.toAlgHom K K A).comp g.ofConv := by
    ext b
    simp
  simp [scalarPoint, AlgHom.mapValue_apply, hs]

private theorem affineGroupConjugationAlgHom_counit
    (g : WithConv (B →ₐ[K] K)) :
    (Bialgebra.counitAlgHom K B).comp (affineGroupConjugationAlgHom g) =
      Bialgebra.counitAlgHom K B := by
  apply WithConv.toConv_injective
  have h := affineGroupConjugationAlgHom_point g
    (toConv (Bialgebra.counitAlgHom K B))
  rw [h]
  have hε : toConv (Bialgebra.counitAlgHom K B) =
      (1 : WithConv (B →ₐ[K] K)) := by
    simp [AlgHom.convOne_def]
  rw [hε]
  group

private theorem affineGroupConjugationAlgHom_comul
    (g : WithConv (B →ₐ[K] K)) :
    (Algebra.TensorProduct.map (affineGroupConjugationAlgHom g)
      (affineGroupConjugationAlgHom g)).comp (Bialgebra.comulAlgHom K B) =
      (Bialgebra.comulAlgHom K B).comp (affineGroupConjugationAlgHom g) := by
  let f := affineGroupConjugationAlgHom g
  let T : Type _ := B ⊗[K] B
  let i₁ : WithConv (B →ₐ[K] T) := toConv Algebra.TensorProduct.includeLeft
  let i₂ : WithConv (B →ₐ[K] T) := toConv Algebra.TensorProduct.includeRight
  let c : WithConv (B →ₐ[K] T) :=
    toConv ((IsScalarTower.toAlgHom K K T).comp g.ofConv)
  have hc (i : WithConv (B →ₐ[K] T)) :
      toConv (i.ofConv.comp f) = c * i * c⁻¹ :=
    affineGroupConjugationAlgHom_point g i
  have hΔ : toConv (Bialgebra.comulAlgHom K B) = i₁ * i₂ := by
    simpa only [i₁, i₂,
      Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom] using
      (Bialgebra.comulPoint_eq_include_mul (R := K) (H := B))
  apply WithConv.toConv_injective
  rw [Bialgebra.toConv_comp_comulAlgHom]
  simp only [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom,
    Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight]
  rw [hc i₁, hc i₂]
  rw [affineGroupConjugationAlgHom_point g
    (toConv (Bialgebra.comulAlgHom K B)), hΔ]
  dsimp [c, T]
  group

/-- Conjugation by one field-valued point is a coordinate Hopf
endomorphism, even though joint conjugation is not a bialgebra map. -/
def affineGroupConjugationBialgHom (g : WithConv (B →ₐ[K] K)) : B →ₐc[K] B :=
  BialgHom.ofAlgHom (affineGroupConjugationAlgHom g)
    (affineGroupConjugationAlgHom_counit g)
    (affineGroupConjugationAlgHom_comul g)

private theorem scalarPoint_inv (g : WithConv (B →ₐ[K] K)) :
    scalarPoint g⁻¹ = (scalarPoint g)⁻¹ := by
  change (AlgHom.mapValue (H := B) (IsScalarTower.toAlgHom K K B)) g⁻¹ = _
  exact map_inv _ g

private theorem affineGroupConjugationAlgHom_comp_inv
    (g : WithConv (B →ₐ[K] K)) :
    (affineGroupConjugationAlgHom g⁻¹).comp
      (affineGroupConjugationAlgHom g) = AlgHom.id K B := by
  apply WithConv.toConv_injective
  calc
    toConv ((affineGroupConjugationAlgHom g⁻¹).comp
        (affineGroupConjugationAlgHom g)) =
        scalarPoint g * toConv (affineGroupConjugationAlgHom g⁻¹) *
          (scalarPoint g)⁻¹ := by
      exact affineGroupConjugationAlgHom_point g
        (toConv (affineGroupConjugationAlgHom g⁻¹))
    _ = toConv (AlgHom.id K B) := by
      rw [affineGroupConjugationAlgHom_conv, scalarPoint_inv]
      group

/-- Conjugation by a fixed original point, bundled as a true coordinate
Hopf automorphism. Its inverse is conjugation by the inverse point. -/
def affineGroupConjugationBialgEquiv (g : WithConv (B →ₐ[K] K)) : B ≃ₐc[K] B :=
  BialgEquiv.ofBialgHom (affineGroupConjugationBialgHom g)
    (affineGroupConjugationBialgHom g⁻¹)
    (by
      ext b
      exact congrArg (fun h : B →ₐ[K] B => h b)
        (by simpa using affineGroupConjugationAlgHom_comp_inv g⁻¹))
    (by
      ext b
      exact congrArg (fun h : B →ₐ[K] B => h b)
        (affineGroupConjugationAlgHom_comp_inv g))

private abbrev C := TauCeti.Bialgebra.CounitAlgebra K B K

private def scalarDualPoint (g : WithConv (B →ₐ[K] K)) :
    WithConv (B →ₐ[K] DualNumber (C (K := K) (B := B))) :=
  toConv ((IsScalarTower.toAlgHom K K _).comp g.ofConv)

private def convFst (u : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    WithConv (B →ₗ[K] C (K := K) (B := B)) :=
  toConv ((TrivSqZeroExt.fstHom K _ _).toLinearMap.comp u.ofConv)

private def convSnd (u : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    WithConv (B →ₗ[K] C (K := K) (B := B)) :=
  toConv ((TrivSqZeroExt.sndHom _ _).restrictScalars K |>.comp u.ofConv)

private theorem convFst_mul
    (u v : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    convFst (u * v) = convFst u * convFst v :=
  congrArg toConv
    (LinearMap.algHom_comp_convMul_distrib (TrivSqZeroExt.fstHom K _ _) u v)

private theorem convSnd_mul
    (u v : WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B)))) :
    convSnd (u * v) = convFst u * convSnd v + convSnd u * convFst v :=
  congrArg toConv (WithConv.snd_comp_convMul u v)

private def pointLinear
    (p : WithConv (B →ₐ[K] DualNumber (C (K := K) (B := B)))) :
    WithConv (B →ₗ[K] DualNumber (C (K := K) (B := B))) :=
  toConv p.ofConv.toLinearMap

private theorem pointLinear_mul
    (p q : WithConv (B →ₐ[K] DualNumber (C (K := K) (B := B)))) :
    pointLinear (p * q) = pointLinear p * pointLinear q :=
  AlgHom.toLinearMap_convMul p q

private theorem convFst_scalarDualPoint (g : WithConv (B →ₐ[K] K)) :
    convFst (pointLinear (scalarDualPoint g)) =
      toConv
        (((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g).ofConv.toLinearMap) := by
  ext a
  simp [convFst, pointLinear, scalarDualPoint,
    TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply,
    TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
  rfl

private theorem convSnd_scalarDualPoint (g : WithConv (B →ₐ[K] K)) :
    convSnd (pointLinear (scalarDualPoint g)) = 0 := by
  ext a
  simp [convSnd, pointLinear, scalarDualPoint]
  change TrivSqZeroExt.snd (TrivSqZeroExt.inl
    (algebraMap K (C (K := K) (B := B)) (g.ofConv a))) = 0
  rfl

private theorem convFst_tangentDualPoint
    (d : Derivation K B (C (K := K) (B := B))) :
    convFst (pointLinear (tangentDualPoint d)) = 1 := by
  ext a
  exact tangentDualPoint_fst d a

private theorem convSnd_tangentDualPoint
    (d : Derivation K B (C (K := K) (B := B))) :
    convSnd (pointLinear (tangentDualPoint d)) = toConv (↑d : B →ₗ[K] C (K := K) (B := B)) := by
  ext a
  exact tangentDualPoint_snd d a

private theorem scalarDualPoint_inv (g : WithConv (B →ₐ[K] K)) :
    scalarDualPoint g⁻¹ = (scalarDualPoint g)⁻¹ := by
  change (AlgHom.mapValue (H := B) (IsScalarTower.toAlgHom K K
    (DualNumber (C (K := K) (B := B))))) g⁻¹ = _
  exact map_inv (AlgHom.mapValue (H := B) (IsScalarTower.toAlgHom K K
    (DualNumber (C (K := K) (B := B))))) g

/-- The differential at the identity of the fixed-point coordinate
conjugation is the original tangent adjoint action. -/
theorem DerivationComp.conjugation
    (g : WithConv (B →ₐ[K] K))
    (d : Derivation K B (C (K := K) (B := B))) :
    TauCeti.derivationComp (B := K) (affineGroupConjugationBialgHom g) d =
      Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) d := by
  let G := (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g
  let P := scalarDualPoint g
  let D := tangentDualPoint d
  have hp : toConv (D.ofConv.comp (affineGroupConjugationAlgHom g)) =
      P * D * (scalarDualPoint g⁻¹) := by
    have h := affineGroupConjugationAlgHom_point g D
    change toConv (D.ofConv.comp (affineGroupConjugationAlgHom g)) =
      P * D * P⁻¹ at h
    rwa [← scalarDualPoint_inv g] at h
  have hl := congrArg pointLinear hp
  rw [pointLinear_mul, pointLinear_mul] at hl
  have hs := congrArg convSnd hl
  rw [convSnd_mul, convFst_mul, convSnd_mul] at hs
  rw [show convFst (pointLinear P) = toConv G.ofConv.toLinearMap from
      convFst_scalarDualPoint g,
    show convSnd (pointLinear P) = 0 from convSnd_scalarDualPoint g,
    show convFst (pointLinear D) = 1 from convFst_tangentDualPoint d,
    show convSnd (pointLinear D) = toConv (↑d : B →ₗ[K] C (K := K) (B := B)) from
      convSnd_tangentDualPoint d,
    show convFst (pointLinear (scalarDualPoint g⁻¹)) =
      toConv (G⁻¹).ofConv.toLinearMap by
        rw [convFst_scalarDualPoint]
        simp [G],
    show convSnd (pointLinear (scalarDualPoint g⁻¹)) = 0 from
      convSnd_scalarDualPoint g⁻¹] at hs
  simp only [mul_one, mul_zero, zero_add, add_zero] at hs
  apply Derivation.ext
  intro a
  have ha := congrArg (fun u : WithConv (B →ₗ[K] C (K := K) (B := B)) =>
    u.ofConv a) hs
  change TrivSqZeroExt.snd (D.ofConv ((affineGroupConjugationAlgHom g) a)) = _ at ha
  rw [tangentDualPoint_snd] at ha
  rw [← Derivation.toConv_coe_adDerivation] at ha
  change d ((affineGroupConjugationAlgHom g) a) =
    Derivation.adDerivation K G d a at ha ⊢
  exact ha

end ReductiveGroups
