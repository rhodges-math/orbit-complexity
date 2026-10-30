import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.AffineMultiplication
import OrbitComplexity.GroupActions.Varieties.AffineGroup

/-! # Tensor coordinates of multiplication

The affine tensor comparison identifies restricted group multiplication with
comultiplication followed by the two coordinate maps.
-/

noncomputable section
namespace SchubertGeometry
open GroupActions CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K H A B : Type u} [Field K]
  [CommRing H] [HopfAlgebra K H] [IsReduced H] [Algebra.FiniteType K H]
  [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
  [CommRing B] [Algebra K B] [IsReduced B] [Algebra.FiniteType K B]
  [IsReduced (A ⊗[K] B)] [Algebra.FiniteType K (A ⊗[K] B)]

omit [IsReduced H] [Algebra.FiniteType K H] [IsReduced A] [Algebra.FiniteType K A]
  [IsReduced B] [Algebra.FiniteType K B] [IsReduced (A ⊗[K] B)]
  [Algebra.FiniteType K (A ⊗[K] B)] in
private theorem conv_factors (f : H →ₐ[K] A) (g : H →ₐ[K] B) :
    ((WithConv.toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).comp f)) *
      (WithConv.toConv ((Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).comp g))).ofConv =
        affineMulMap f g := by
  have ht : (Algebra.TensorProduct.lmul' K).comp
      (Algebra.TensorProduct.map
        ((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).comp f)
        ((Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).comp g)) =
      Algebra.TensorProduct.map f g := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  rw [AlgHom.convMul_def, ← AlgHom.comp_assoc, ht]
  rfl

/-- The affine tensor-product comparison carries restricted multiplication to its coordinate map. -/
theorem affineTensorIso_mul (f : H →ₐ[K] A) (g : H →ₐ[K] B) :
    (affineTensorIso K A B).hom ≫
      ((fst (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism f) *
        (snd (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism g)) =
      affineMorphism (affineMulMap f g) := by
  let l := (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).comp f
  let r := (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).comp g
  have hl : (affineTensorIso K A B).hom ≫
      (fst (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism f) =
        affineMorphism l := by
    rw [← Category.assoc, affineTensorIso_fst]
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom l.toRingHom)
    rw [← Spec.map_comp]
    rfl
  have hr : (affineTensorIso K A B).hom ≫
      (snd (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism g) =
        affineMorphism r := by
    rw [← Category.assoc, affineTensorIso_snd]
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom r.toRingHom)
    rw [← Spec.map_comp]
    rfl
  have hm : affineMorphism
      ((WithConv.toConv l) * (WithConv.toConv r)).ofConv =
        affineMorphism l * affineMorphism r := by
    let e : WithConv (H →ₐ[K] A ⊗[K] B) ≃*
        ((Spec (CommRingCat.of (A ⊗[K] B))).asOver (Spec (CommRingCat.of K)) ⟶
          (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of K))) := Spec.mapMulEquiv
    apply Over.OverMorphism.ext
    change (e ((WithConv.toConv l) * (WithConv.toConv r))).left =
      ((e (WithConv.toConv l)) * (e (WithConv.toConv r))).left
    exact congrArg (fun q => q.left) (map_mul e _ _)
  calc
    _ = ((affineTensorIso K A B).hom ≫
        (fst (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism f)) *
        ((affineTensorIso K A B).hom ≫
          (snd (affineVariety K A).toOver (affineVariety K B).toOver ≫ affineMorphism g)) :=
      MonObj.comp_mul _ _ _
    _ = affineMorphism l * affineMorphism r := congrArg₂ (· * ·) hl hr
    _ = _ := hm.symm.trans (congrArg affineMorphism (conv_factors f g))

end SchubertGeometry
