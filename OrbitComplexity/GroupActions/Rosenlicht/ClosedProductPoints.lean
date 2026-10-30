import OrbitComplexity.GroupActions.Rosenlicht.AffineSchemePoints
import OrbitComplexity.GroupActions.Rosenlicht.ClosedTensorPoints
import OrbitComplexity.GroupActions.Rosenlicht.AffineProductCoordinates

/-!
# ClosedProductPoints
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v

private abbrev productCoordinateAlgebra (R : CommRingCat.{u}) (Y : Scheme.{u})
    [Y.Over (Spec R)] [IsAffine Y] : Algebra R Γ(Y, ⊤) := inferInstance

private theorem isoClosed {S T : Scheme.{u}} (e : S ≅ T) : IsClosedImmersion e.hom :=
  inferInstance

variable (K : Type u) [Field K] (Y W : Scheme.{u})
variable [Y.Over (Spec (.of K))] [W.Over (Spec (.of K))] [IsAffine Y] [IsAffine W]
variable {Z : Scheme.{u}}

/-- Rational points of a closed affine correspondence lift from pairs of
factor points annihilating the full relation ideal of second-coordinate generators. -/
theorem closedProductPoint_lift
    (i : Z ⟶ pullback (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) [IsClosedImmersion i]
    {ι : Type v} (c : ι → Γ(W, ⊤))
    (hc : letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
      Algebra.adjoin K (Set.range c) = ⊤)
    (p : {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _})
    (q : {q : Spec (.of K) ⟶ W // q ≫ (W ↘ Spec (.of K)) = 𝟙 _}) :
    letI : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
    letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
    let j := i ≫ (affineProductSpecIso (.of K) Y W).hom
    let φ := tensorCoordinateMap j
    letI : Algebra Γ(Y, ⊤) Γ(Z, ⊤) :=
      (φ.comp (Algebra.TensorProduct.includeLeft :
        Γ(Y, ⊤) →ₐ[K] Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom).toAlgebra
    let f : MvPolynomial ι Γ(Y, ⊤) →ₐ[Γ(Y, ⊤)] Γ(Z, ⊤) :=
      MvPolynomial.aeval (fun a ↦ φ ((1 : Γ(Y, ⊤)) ⊗ₜ[K] c a))
    RingHom.ker f ≤ RingHom.ker (MvPolynomial.eval₂Hom
      ((affineSchemePointsEquiv K Y) p).toRingHom
      (fun a ↦ ((affineSchemePointsEquiv K W) q) (c a))) →
      ∃ r : Spec (.of K) ⟶ Z,
        r ≫ i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K)) = p.val ∧
        r ≫ i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K)) = q.val := by
  let : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
  let : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
  let j := i ≫ (affineProductSpecIso (.of K) Y W).hom
  let φ := tensorCoordinateMap j
  let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) :=
    (φ.comp (Algebra.TensorProduct.includeLeft :
      Γ(Y, ⊤) →ₐ[K] Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom).toAlgebra
  let f : MvPolynomial ι Γ(Y, ⊤) →ₐ[Γ(Y, ⊤)] Γ(Z, ⊤) :=
    MvPolynomial.aeval (fun a ↦ φ ((1 : Γ(Y, ⊤)) ⊗ₜ[K] c a))
  change RingHom.ker f ≤ RingHom.ker (MvPolynomial.eval₂Hom
    ((affineSchemePointsEquiv K Y) p).toRingHom
    (fun a ↦ ((affineSchemePointsEquiv K W) q) (c a))) → _
  intro hrel
  have : IsClosedImmersion j :=
    @IsClosedImmersion.comp _ _ _ i (affineProductSpecIso (.of K) Y W).hom
      inferInstance (isoClosed (affineProductSpecIso (.of K) Y W))
  let x := (affineSchemePointsEquiv K Y) p
  let y := (affineSchemePointsEquiv K W) q
  let pair := Algebra.TensorProduct.lift x y (fun _ _ ↦ Commute.all _ _)
  obtain ⟨r, hr⟩ := closedTensorPoint_lift j c hc x y hrel
  have hj₁ : j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(Y, ⊤) →ₐ[K]
        Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) =
      (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) ≫ Y.isoSpec.hom := by
    dsimp only [j]
    erw [Category.assoc, affineProductSpecIso_fst, ← Category.assoc]
  have hj₂ : j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(W, ⊤) →ₐ[K]
        Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) =
      (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) ≫ W.isoSpec.hom := by
    dsimp only [j]
    erw [Category.assoc, affineProductSpecIso_snd, ← Category.assoc]
  refine ⟨r, ?_, ?_⟩
  · apply (cancel_mono Y.isoSpec.hom).mp
    calc
      _ = (r ≫ j) ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : Γ(Y, ⊤) →ₐ[K]
            Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) := by
        simpa only [Category.assoc] using congrArg (fun a ↦ r ≫ a) hj₁.symm
      _ = Spec.map (CommRingCat.ofHom x.toRingHom) := by
        rw [hr, ← Spec.map_comp]
        congr 1
        ext a
        change pair (a ⊗ₜ[K] 1) = x a
        simp only [pair, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      _ = _ := affineSchemePointsEquiv_spec K Y p
  · apply (cancel_mono W.isoSpec.hom).mp
    calc
      _ = (r ≫ j) ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(W, ⊤) →ₐ[K]
            Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) := by
        simpa only [Category.assoc] using congrArg (fun a ↦ r ≫ a) hj₂.symm
      _ = Spec.map (CommRingCat.ofHom y.toRingHom) := by
        rw [hr, ← Spec.map_comp]
        congr 1
        ext a
        change pair (1 ⊗ₜ[K] a) = y a
        simp only [pair, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      _ = _ := affineSchemePointsEquiv_spec K W q

private lemma productTensor_left
    (i : Z ⟶ pullback (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) (a : Γ(Y, ⊤)) :
    letI : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
    letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
    tensorCoordinateMap (i ≫ (affineProductSpecIso (.of K) Y W).hom)
      (a ⊗ₜ[K] (1 : Γ(W, ⊤))) =
        (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop a := by
  let : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
  let : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
  rw [tensorCoordinateMap_left]
  have hj : (i ≫ (affineProductSpecIso (.of K) Y W).hom) ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(Y, ⊤) →ₐ[K]
        Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) =
      (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) ≫ Y.isoSpec.hom := by
    erw [Category.assoc, affineProductSpecIso_fst, ← Category.assoc]
  rw [hj, Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (Y.toSpecΓ.appTop ≫
    (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop)) a = _
  rw [Scheme.toSpecΓ_appTop, ← Category.assoc]
  simp only [Iso.inv_hom_id, Category.id_comp]

private lemma productTensor_right
    (i : Z ⟶ pullback (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) (b : Γ(W, ⊤)) :
    letI : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
    letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
    tensorCoordinateMap (i ≫ (affineProductSpecIso (.of K) Y W).hom)
      ((1 : Γ(Y, ⊤)) ⊗ₜ[K] b) =
        (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop b := by
  let : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
  let : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
  rw [tensorCoordinateMap_right]
  have hj : (i ≫ (affineProductSpecIso (.of K) Y W).hom) ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(W, ⊤) →ₐ[K]
        Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom) =
      (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) ≫ W.isoSpec.hom := by
    erw [Category.assoc, affineProductSpecIso_snd, ← Category.assoc]
  rw [hj, Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso Γ(W, ⊤)).inv ≫ (W.toSpecΓ.appTop ≫
    (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop)) b = _
  rw [Scheme.toSpecΓ_appTop, ← Category.assoc]
  simp only [Iso.inv_hom_id, Category.id_comp]

/-- Polynomial equations written directly in the two scheme projections
characterize pairs lifting to a closed affine correspondence. -/
theorem closedProductPoint_exists
    (i : Z ⟶ pullback (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))) [IsClosedImmersion i]
    {ι : Type v} (c : ι → Γ(W, ⊤))
    (hc : letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
      Algebra.adjoin K (Set.range c) = ⊤)
    (p : {p : Spec (.of K) ⟶ Y // p ≫ (Y ↘ Spec (.of K)) = 𝟙 _})
    (q : {q : Spec (.of K) ⟶ W // q ≫ (W ↘ Spec (.of K)) = 𝟙 _}) :
    letI : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
    letI : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
    RingHom.ker (MvPolynomial.eval₂Hom
      (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop.hom
      (fun a ↦ (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop (c a))) ≤
        RingHom.ker (MvPolynomial.eval₂Hom
          ((affineSchemePointsEquiv K Y) p).toRingHom
          (fun a ↦ ((affineSchemePointsEquiv K W) q) (c a))) →
      ∃ r : Spec (.of K) ⟶ Z,
        r ≫ i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K)) = p.val ∧
        r ≫ i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K)) = q.val := by
  let : Algebra K Γ(Y, ⊤) := productCoordinateAlgebra (.of K) Y
  let : Algebra K Γ(W, ⊤) := productCoordinateAlgebra (.of K) W
  intro hrel
  apply closedProductPoint_lift K Y W i c hc p q
  let j := i ≫ (affineProductSpecIso (.of K) Y W).hom
  let φ := tensorCoordinateMap j
  let : Algebra Γ(Y, ⊤) Γ(Z, ⊤) :=
    (φ.comp (Algebra.TensorProduct.includeLeft :
      Γ(Y, ⊤) →ₐ[K] Γ(Y, ⊤) ⊗[K] Γ(W, ⊤)).toRingHom).toAlgebra
  let f : MvPolynomial ι Γ(Y, ⊤) →ₐ[Γ(Y, ⊤)] Γ(Z, ⊤) :=
    MvPolynomial.aeval (fun a ↦ φ ((1 : Γ(Y, ⊤)) ⊗ₜ[K] c a))
  change RingHom.ker f ≤ _
  have he : f.toRingHom = MvPolynomial.eval₂Hom
      (i ≫ pullback.fst (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop.hom
      (fun a ↦ (i ≫ pullback.snd (Y ↘ Spec (.of K)) (W ↘ Spec (.of K))).appTop (c a)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [MvPolynomial.eval₂Hom_C]
      change f (MvPolynomial.C a) = _
      have hf := f.commutes a
      change f (MvPolynomial.C a) = φ (a ⊗ₜ[K] 1) at hf
      exact hf.trans (productTensor_left K Y W i a)
    · intro a
      simp only [MvPolynomial.eval₂Hom_X']
      change f (MvPolynomial.X a) = _
      simp only [f, MvPolynomial.aeval_X]
      exact productTensor_right K Y W i (c a)
  change RingHom.ker f.toRingHom ≤ _
  rw [he]
  exact hrel

end

end GroupActions
