import OrbitComplexity.GroupActions.Rosenlicht.AffineCorrespondenceFields
import OrbitComplexity.GroupActions.Rosenlicht.TensorPointLifts

/-!
# ClosedTensorPoints
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v

variable {K A B : Type u} [Field K]
variable [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
variable {Z : Scheme.{u}}

/-- The spectrum of a tensor-coordinate homomorphism is the given morphism
precomposed with the inverse affine-spectrum isomorphism. -/
theorem tensorCoordinateMap_spec [IsAffine Z]
    (i : Z ⟶ Spec (.of (A ⊗[K] B))) :
    Spec.map (CommRingCat.ofHom (tensorCoordinateMap i)) = Z.isoSpec.inv ≫ i := by
  apply (cancel_mono (Spec (.of (A ⊗[K] B))).toSpecΓ).mp
  change Spec.map ((Scheme.ΓSpecIso (.of (A ⊗[K] B))).inv ≫ i.appTop) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, SpecMap_ΓSpecIso_inv_toSpecΓ, Category.comp_id]
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc]
  change Spec.map i.appTop = (Z.isoSpec.inv ≫ Z.isoSpec.hom) ≫ Spec.map i.appTop
  rw [Iso.inv_hom_id, Category.id_comp]

/-- A pair of algebra points lifts to a closed tensor correspondence when
it annihilates the full polynomial relation ideal of second-factor generators. -/
theorem closedTensorPoint_lift
    (i : Z ⟶ Spec (.of (A ⊗[K] B))) [IsClosedImmersion i]
    {ι : Type v} (c : ι → B) (hc : Algebra.adjoin K (Set.range c) = ⊤)
    (x : A →ₐ[K] K) (y : B →ₐ[K] K) :
    let φ := tensorCoordinateMap i
    letI : Algebra A Γ(Z, ⊤) :=
      (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom).toAlgebra
    let f : MvPolynomial ι A →ₐ[A] Γ(Z, ⊤) :=
      MvPolynomial.aeval (fun j ↦ φ ((1 : A) ⊗ₜ[K] c j))
    RingHom.ker f ≤ RingHom.ker (MvPolynomial.eval₂Hom x.toRingHom (fun j ↦ y (c j))) →
      ∃ q : Spec (.of K) ⟶ Z, q ≫ i =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lift x y (fun _ _ ↦ Commute.all _ _)).toRingHom) := by
  let φ := tensorCoordinateMap i
  let : Algebra A Γ(Z, ⊤) :=
    (φ.comp (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom).toAlgebra
  let f : MvPolynomial ι A →ₐ[A] Γ(Z, ⊤) :=
    MvPolynomial.aeval (fun j ↦ φ ((1 : A) ⊗ₜ[K] c j))
  change RingHom.ker f ≤ RingHom.ker
    (MvPolynomial.eval₂Hom x.toRingHom (fun j ↦ y (c j))) → _
  intro hrel
  obtain ⟨ρ, hρ⟩ := exists_tensorPoint_factor K A B Γ(Z, ⊤) φ
    (tensorCoordinateMap_surjective i) c hc x y hrel
  have : IsAffine Z := isAffine_of_isAffineHom i
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ Z.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← tensorCoordinateMap_spec, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (ρ.comp φ)) = _
  rw [hρ]

end

end GroupActions
