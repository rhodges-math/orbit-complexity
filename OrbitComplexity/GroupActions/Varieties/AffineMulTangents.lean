import OrbitComplexity.GroupActions.Varieties.AffineMultiplication
import OrbitComplexity.GroupActions.Varieties.PointHopfTangents

/-! # The differential of affine multiplication

The two counit projections recover the factor maps from restricted multiplication.
At the identity this identifies the differential with addition of the two included tangents.

## Main results

* `GroupActions.projectLeft_comp_affineMulMap`: the first counit projection recovers its factor.
* `GroupActions.projectRight_comp_affineMulMap`: the second counit projection recovers its factor.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u

variable {R H A B : Type u} [CommRing R] [CommRing H] [CommRing A] [CommRing B]
  [Bialgebra R H] [Bialgebra R A] [Bialgebra R B]

/-- The first counit projection of restricted multiplication is its first coordinate map. -/
theorem projectLeft_comp_affineMulMap (f : H →ₐc[R] A) (g : H →ₐc[R] B) :
    (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := A) (H₂ := B)).toAlgHom.comp
      (affineMulMap f.toAlgHom g.toAlgHom) = f.toAlgHom := by
  let φ : H ⊗[R] H →ₐ[R] A :=
    (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := A) (H₂ := B)).toAlgHom.comp
      (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom)
  have hleft : φ.comp Algebra.TensorProduct.includeLeft = f.toAlgHom := by
    ext h
    simp [φ, TauCeti.Bialgebra.TensorProduct.projectLeft_tmul]
  have hright : φ.comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R H) := by
    ext h
    simp [φ, TauCeti.Bialgebra.TensorProduct.projectLeft_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def]
  have h := TauCeti.Bialgebra.toConv_comp_comulAlgHom φ
  simp only [TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom,
    TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom] at h
  change WithConv.toConv (φ.comp (Bialgebra.comulAlgHom R H)) =
    WithConv.toConv (φ.comp Algebra.TensorProduct.includeLeft) *
      WithConv.toConv (φ.comp Algebra.TensorProduct.includeRight) at h
  rw [hleft, hright] at h
  change WithConv.toConv (φ.comp (Bialgebra.comulAlgHom R H)) =
    WithConv.toConv f.toAlgHom * 1 at h
  rw [mul_one] at h
  exact congrArg WithConv.ofConv h

/-- The second counit projection of restricted multiplication is its second coordinate map. -/
theorem projectRight_comp_affineMulMap (f : H →ₐc[R] A) (g : H →ₐc[R] B) :
    (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := A) (H₂ := B)).toAlgHom.comp
      (affineMulMap f.toAlgHom g.toAlgHom) = g.toAlgHom := by
  let φ : H ⊗[R] H →ₐ[R] B :=
    (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := A) (H₂ := B)).toAlgHom.comp
      (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom)
  have hleft : φ.comp Algebra.TensorProduct.includeLeft =
      (Algebra.ofId R B).comp (Bialgebra.counitAlgHom R H) := by
    ext h
    simp [φ, TauCeti.Bialgebra.TensorProduct.projectRight_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def]
  have hright : φ.comp Algebra.TensorProduct.includeRight = g.toAlgHom := by
    ext h
    simp [φ, TauCeti.Bialgebra.TensorProduct.projectRight_tmul]
  have h := TauCeti.Bialgebra.toConv_comp_comulAlgHom φ
  simp only [TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom,
    TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom] at h
  change WithConv.toConv (φ.comp (Bialgebra.comulAlgHom R H)) =
    WithConv.toConv (φ.comp Algebra.TensorProduct.includeLeft) *
      WithConv.toConv (φ.comp Algebra.TensorProduct.includeRight) at h
  rw [hleft, hright] at h
  change WithConv.toConv (φ.comp (Bialgebra.comulAlgHom R H)) =
    1 * WithConv.toConv g.toAlgHom at h
  rw [one_mul] at h
  exact congrArg WithConv.ofConv h

/-- Restricted multiplication takes the counit point of its product to the counit point. -/
theorem counit_comp_affineMulMap (f : H →ₐc[R] A) (g : H →ₐc[R] B) :
    (Bialgebra.counitAlgHom R (A ⊗[R] B)).comp (affineMulMap f.toAlgHom g.toAlgHom) =
      Bialgebra.counitAlgHom R H := by
  rw [← BialgHom.counitAlgHom_comp
    (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := A) (H₂ := B)),
    AlgHom.comp_assoc, projectLeft_comp_affineMulMap, BialgHom.counitAlgHom_comp]


/-- The identity differential of multiplication restricted to two affine factors. -/
def affineMulTangent (f : H →ₐc[R] A) (g : H →ₐc[R] B) :
    Derivation R (A ⊗[R] B) (TauCeti.Bialgebra.CounitAlgebra R (A ⊗[R] B) R) →ₗ[R]
      Derivation R H (TauCeti.Bialgebra.CounitAlgebra R H R) :=
  (counitPointDerivEquiv R H).toLinearMap.comp
    ((pointDerivationCongr (counit_comp_affineMulMap f g)).toLinearMap.comp
      ((pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
        (Bialgebra.counitAlgHom R (A ⊗[R] B))).comp
        (counitPointDerivEquiv R (A ⊗[R] B)).symm.toLinearMap))

/-- The multiplication differential precomposes a tangent derivation with the coordinate map. -/
@[simp]
theorem affineMulTangent_apply (f : H →ₐc[R] A) (g : H →ₐc[R] B)
    (d : Derivation R (A ⊗[R] B) (TauCeti.Bialgebra.CounitAlgebra R (A ⊗[R] B) R)) (h : H) :
    affineMulTangent f g d h = d (affineMulMap f.toAlgHom g.toAlgHom h) := by
  change counitPointDerivEquiv R H
    (pointDerivationCongr (counit_comp_affineMulMap f g)
      (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
        (Bialgebra.counitAlgHom R (A ⊗[R] B))
        ((counitPointDerivEquiv R (A ⊗[R] B)).symm d))) h = _
  erw [counitPointDerivEquiv_apply, pointDerivationCongr_apply,
    pointDerivationPrecomp_apply, counitPointDerivEquiv_symm_apply]

/-- Under the product tangent equivalence, the multiplication differential adds the two images. -/
theorem affineMulTangent_prod (f : H →ₐc[R] A) (g : H →ₐc[R] B)
    (d : Derivation R A (TauCeti.Bialgebra.CounitAlgebra R A R) ×
      Derivation R B (TauCeti.Bialgebra.CounitAlgebra R B R)) :
    affineMulTangent f g
        ((Derivation.tensorProductLieEquiv (R := R) (B := R) (H₁ := A) (H₂ := B)).symm d) =
      TauCeti.derivationComp f d.1 + TauCeti.derivationComp g d.2 := by
  ext h
  apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  rw [Derivation.add_apply, map_add, TauCeti.algEquivSelf_derivationComp_apply,
    TauCeti.algEquivSelf_derivationComp_apply]
  have hf := AlgHom.congr_fun (projectLeft_comp_affineMulMap f g) h
  have hg := AlgHom.congr_fun (projectRight_comp_affineMulMap f g) h
  simp only [AlgHom.comp_apply] at hf hg
  have hp := congrArg (fun δ => TauCeti.Bialgebra.CounitAlgebra.algEquivSelf R
      (A ⊗[R] B) R (δ (affineMulMap f.toAlgHom g.toAlgHom h)))
    (Derivation.tensorProductLieEquiv_symm_apply (R := R) (B := R) d)
  simp only [Derivation.add_apply, map_add, TauCeti.algEquivSelf_derivationComp_apply] at hp
  erw [hf, hg] at hp
  calc
    _ = TauCeti.Bialgebra.CounitAlgebra.algEquivSelf R (A ⊗[R] B) R
        (((Derivation.tensorProductLieEquiv (R := R) (B := R)
          (H₁ := A) (H₂ := B)).symm d) (affineMulMap f.toAlgHom g.toAlgHom h)) := by
      erw [affineMulTangent_apply]
      rfl
    _ = _ := hp

/-- The multiplication differential is bijective exactly when addition of tangent images is. -/
theorem affineMulTangent_bijective_iff (f : H →ₐc[R] A) (g : H →ₐc[R] B) :
    Function.Bijective (affineMulTangent f g) ↔
      Function.Bijective (fun d : Derivation R A (TauCeti.Bialgebra.CounitAlgebra R A R) ×
        Derivation R B (TauCeti.Bialgebra.CounitAlgebra R B R) =>
          TauCeti.derivationComp f d.1 + TauCeti.derivationComp g d.2) := by
  let e := (Derivation.tensorProductLieEquiv (R := R) (B := R) (H₁ := A) (H₂ := B)).toLinearEquiv
  have hcomp : affineMulTangent f g ∘ e.symm =
      (fun d : Derivation R A (TauCeti.Bialgebra.CounitAlgebra R A R) ×
        Derivation R B (TauCeti.Bialgebra.CounitAlgebra R B R) =>
          TauCeti.derivationComp f d.1 + TauCeti.derivationComp g d.2) :=
    funext (affineMulTangent_prod f g)
  rw [← hcomp]
  exact (EquivLike.bijective_comp e.symm (affineMulTangent f g)).symm

end

end GroupActions
