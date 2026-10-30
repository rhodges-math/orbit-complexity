import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionProduct
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionIso
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionCoordinates
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupParabolicTangent
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct

/-! # Geometric Levi multiplication for standard parabolics

The closed factors have disjoint tangent images. Smoothness and unique factors on rational
points identify the product morphism with an isomorphism of varieties.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private abbrev pIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (standardParabolicPoints G I)
private abbrev rIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I)

private theorem pIdeal_le_levi (I : Set G.rootBase.support) :
    pIdeal G I ≤ G.leviIdeal I := by
  intro a ha
  apply (HopfIdeal.mem_vanishingIdeal (G.leviPoints I) a).mpr
  intro l
  have hl : l.val ∈ standardParabolicPoints G I := by
    rw [parabolic_eq_levi_sup_unipotent]
    exact (show G.leviPoints I ≤ _ from le_sup_left) l.property
  exact (HopfIdeal.mem_vanishingIdeal (standardParabolicPoints G I) a).mp ha ⟨l.val, hl⟩

private theorem pReduced (I : Set G.rootBase.support) : IsReduced (parabolicAlgebra G I) := by
  change IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)))
  infer_instance

private theorem lSmooth (I : Set G.rootBase.support) : Algebra.Smooth K (G.leviAlgebra I) :=
  G.levi_smooth I

private theorem lDomain (I : Set G.rootBase.support) : IsDomain (G.leviAlgebra I) := by
  apply (affine_isIntegral_iff (CommRingCat.of (G.leviAlgebra I))).mp
  change IsIntegral (reductiveVariety (leviGroupData G I)).scheme
  infer_instance
attribute [local instance] pReduced lSmooth lDomain

private theorem pFinite (I : Set G.rootBase.support) :
    Algebra.FiniteType K (parabolicAlgebra G I) := by
  change Algebra.FiniteType K (G.coordinateAlgebra ⧸ (pIdeal G I).toIdeal)
  infer_instance
attribute [local instance] pFinite

private theorem pSmooth (I : Set G.rootBase.support) :
    Algebra.Smooth K (parabolicAlgebra G I) :=
  (smoothCommHopfAlgProperty_iff (parabolicAlgebra G I).obj).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)

private theorem rSmooth (I : Set G.rootBase.support) :
    Algebra.Smooth K (G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I)) :=
  (smoothCommHopfAlgProperty_iff (CommHopfAlgCat.of K (G.rootSubsetAlgebra _ _))).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K _)
attribute [local instance] pSmooth rSmooth

private theorem rReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (rIdeal G I).toIdeal) := by
  change IsReduced (G.rootSubsetAlgebra _ _)
  infer_instance
attribute [local instance] rReduced

private theorem pIdeal_le_root (I : Set G.rootBase.support) : pIdeal G I ≤ rIdeal G I := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro r hr
  apply ((HopfIdeal.le_vanishingIdeal_iff _ (pIdeal G I)).mp le_rfl)
  rw [parabolic_eq_levi_sup_unipotent]
  exact (show parabolicUnipotentPoints G I ≤ _ from le_sup_right) hr

private abbrev qP (I : Set G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] parabolicAlgebra G I :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (pIdeal G I)).hom
private abbrev qL (I : Set G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] G.leviAlgebra I :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (G.leviIdeal I)).hom
private abbrev qR (I : Set G.rootBase.support) :
    G.coordinateAlgebra →ₐc[K] G.rootSubsetAlgebra
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj (rIdeal G I)).hom
private abbrev factorL (I : Set G.rootBase.support) :
    parabolicAlgebra G I →ₐc[K] G.leviAlgebra I :=
  (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj (pIdeal_le_levi G I)).hom
private abbrev factorR (I : Set G.rootBase.support) :
    parabolicAlgebra G I →ₐc[K] G.rootSubsetAlgebra
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) :=
  (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj (pIdeal_le_root G I)).hom

private theorem factorL_comp (I : Set G.rootBase.support) :
    (factorL G I).comp (qP G I) = qL G I := by
  ext a
  exact CommHopfAlgCat.quotientMapOfLe_mk G.coordinateAlgebra.obj (pIdeal_le_levi G I) a

private theorem factorR_comp (I : Set G.rootBase.support) :
    (factorR G I).comp (qP G I) = qR G I := by
  ext a
  exact CommHopfAlgCat.quotientMapOfLe_mk G.coordinateAlgebra.obj (pIdeal_le_root G I) a

private theorem factorTangents_disjoint (I : Set G.rootBase.support) :
    Disjoint (derivationComp (B := K) (factorL G I)).range
      (derivationComp (B := K) (factorR G I)).range := by
  rw [disjoint_iff]
  apply eq_bot_iff.mpr
  intro d hd
  obtain ⟨l, hl⟩ := hd.1
  obtain ⟨r, hr⟩ := hd.2
  have hL : derivationComp (B := K) (qP G I) d ∈
      G.subgroupTangent (G.leviIdeal I) := by
    refine ⟨l, ?_⟩
    change derivationComp (B := K) (qL G I) l = derivationComp (B := K) (qP G I) d
    calc
      _ = derivationComp (B := K) ((factorL G I).comp (qP G I)) l :=
        (congrArg (fun f : G.coordinateAlgebra →ₐc[K] G.leviAlgebra I =>
          derivationComp (B := K) f l) (factorL_comp G I)).symm
      _ = derivationComp (B := K) (qP G I) (derivationComp (B := K) (factorL G I) l) :=
        congrArg (fun f => f l) (derivationComp_comp (B := K) (factorL G I) (qP G I))
      _ = _ := congrArg (derivationComp (B := K) (qP G I)) hl
  have hR : derivationComp (B := K) (qP G I) d ∈
      G.subgroupTangent (rIdeal G I) := by
    refine ⟨r, ?_⟩
    change derivationComp (B := K) (qR G I) r = derivationComp (B := K) (qP G I) d
    calc
      _ = derivationComp (B := K) ((factorR G I).comp (qP G I)) r :=
        (congrArg (fun f : G.coordinateAlgebra →ₐc[K] G.rootSubsetAlgebra
          (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I) =>
            derivationComp (B := K) f r) (factorR_comp G I)).symm
      _ = derivationComp (B := K) (qP G I) (derivationComp (B := K) (factorR G I) r) :=
        congrArg (fun f => f r) (derivationComp_comp (B := K) (factorR G I) (qP G I))
      _ = _ := congrArg (derivationComp (B := K) (qP G I)) hr
  have hz : derivationComp (B := K) (qP G I) d = 0 :=
    Submodule.disjoint_def.mp (G.levi_disjoint_parabolicTangent I) _ hL hR
  apply derivationComp_injective_of_surjective (qP G I)
    (CommHopfAlgCat.mkQuotient_surjective _ _)
  simpa only [map_zero] using hz

private theorem productDomain (I : Set G.rootBase.support) :
    IsDomain (G.leviAlgebra I ⊗[K] G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I)) :=
  isDomain_tensorProduct

private theorem productFinite (I : Set G.rootBase.support) :
    Algebra.FiniteType K (G.leviAlgebra I ⊗[K] G.rootSubsetAlgebra
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I)) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K (G.leviAlgebra I))
    (inferInstance : Algebra.FiniteType (G.leviAlgebra I) _)
attribute [local instance] productDomain productFinite

private abbrev productAffine (I : Set G.rootBase.support) : Variety K :=
  affineVariety K (G.leviAlgebra I ⊗[K] G.rootSubsetAlgebra
    (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I))

private def tensorIso (I : Set G.rootBase.support) :
    (productAffine G I).toOver ≅ (parabolicLeviProduct G I).toOver :=
  affineTensorIso K (G.leviAlgebra I) (G.rootSubsetAlgebra
    (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I))

private abbrev coordinate (I : Set G.rootBase.support) : parabolicAlgebra G I →ₐ[K]
    G.leviAlgebra I ⊗[K] G.rootSubsetAlgebra (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I) :=
  affineMulMap (factorL G I).toAlgHom (factorR G I).toAlgHom

private abbrev coordinateHom (I : Set G.rootBase.support) :
    (productAffine G I).toOver ⟶ (standardParabolicVariety G I).toOver := by
  let : Algebra.FiniteType K (parabolicAlgebra G I) := pFinite G I
  exact affineMorphism (K := K) (A := parabolicAlgebra G I) (coordinate G I)

private theorem tensorIso_comp (I : Set G.rootBase.support) :
    (tensorIso G I).hom ≫ parabolicMultiplication G I = coordinateHom G I := by
  have hl : leviParabolicInclusion G I = affineMorphism (factorL G I).toAlgHom := by
    apply Over.OverMorphism.ext
    rfl
  have hr : parabolicUnipotentInclusion G I = affineMorphism (factorR G I).toAlgHom := by
    apply Over.OverMorphism.ext
    rfl
  have hl' := congrArg (fun f : (leviVariety G I).toOver ⟶
      (standardParabolicVariety G I).toOver =>
        fst (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver ≫ f) hl
  have hr' := congrArg (fun f : (parabolicUnipotentVariety G I).toOver ⟶
      (standardParabolicVariety G I).toOver =>
        snd (leviVariety G I).toOver (parabolicUnipotentVariety G I).toOver ≫ f) hr
  have hm := congrArg₂ (fun (f g : (parabolicLeviProduct G I).toOver ⟶
      (standardParabolicVariety G I).toOver) => f * g) hl' hr'
  have hc := congrArg (fun f : (parabolicLeviProduct G I).toOver ⟶
      (standardParabolicVariety G I).toOver => (tensorIso G I).hom ≫ f) hm
  exact hc.trans (affineTensorIso_mul (factorL G I).toAlgHom (factorR G I).toAlgHom)

attribute [local irreducible] tensorIso

omit [IsAlgClosed K] [CharZero K] in
private theorem iso_points_bijective {X Y : Variety K} (e : X.toOver ≅ Y.toOver) :
    Function.Bijective (Variety.mapPoints e.hom) :=
  (Variety.pointsHomeomorph e).bijective

omit [IsAlgClosed K] [CharZero K] in
private theorem points_bijective_comp {X Y Z : Variety K}
    (e : X.toOver ≅ Y.toOver) (f : Y.toOver ⟶ Z.toOver)
    (hf : Function.Bijective (Variety.mapPoints f)) :
    Function.Bijective (Variety.mapPoints (X := X) (Y := Z) (e.hom ≫ f)) := by
  have he := iso_points_bijective (X := X) (Y := Y) e
  have hc : Variety.mapPoints (X := X) (Y := Z) (e.hom ≫ f) =
      Variety.mapPoints (X := Y) (Y := Z) f ∘
        Variety.mapPoints (X := X) (Y := Y) e.hom :=
    funext (Variety.mapPoints_comp (X := X) (Y := Y) (Z := Z) e.hom f)
  exact hc.symm ▸ (hf.comp he)

private theorem affine_points_bijective (I : Set G.rootBase.support) :
    Function.Bijective (Variety.mapPoints (X := productAffine G I)
      (Y := standardParabolicVariety G I) (coordinateHom G I)) := by
  have h := points_bijective_comp (X := productAffine G I)
    (Y := parabolicLeviProduct G I) (Z := standardParabolicVariety G I)
    (tensorIso G I) (parabolicMultiplication G I) (parabolicMultiplication_bijective G I)
  have he := congrArg (fun f : (productAffine G I).toOver ⟶
      (standardParabolicVariety G I).toOver =>
        Function.Bijective (Variety.mapPoints (X := productAffine G I)
          (Y := standardParabolicVariety G I) f)) (tensorIso_comp G I)
  exact he ▸ h

omit [IsAlgClosed K] [CharZero K] in
private theorem bijective_coordinates {D C : Type u} [CommRing D] [Algebra K D]
    [IsReduced D] [Algebra.FiniteType K D] [CommRing C] [Algebra K C]
    [IsReduced C] [Algebra.FiniteType K C] (f : D →ₐ[K] C)
    (h : Function.Bijective (Variety.mapPoints (affineMorphism f))) :
    Function.Bijective (fun p : C →ₐ[K] K => p.comp f) := by
  let e := affineVarietyPointsEquiv K C
  let eD := affineVarietyPointsEquiv K D
  constructor
  · intro a b hab
    apply e.symm.injective
    apply h.1
    rw [affineMorphism_points, affineMorphism_points]
    exact congrArg eD.symm hab
  · intro p
    obtain ⟨q, hq⟩ := h.2 (eD.symm p)
    obtain ⟨r, rfl⟩ := e.symm.surjective q
    refine ⟨r, ?_⟩
    rw [affineMorphism_points] at hq
    exact eD.symm.injective hq

private theorem coordinate_points_bijective (I : Set G.rootBase.support) :
    Function.Bijective (fun p : (G.leviAlgebra I ⊗[K] G.rootSubsetAlgebra
      (parabolicRadicalRoots G.rootBase I) (parabolicRadicalRoots_closed G.rootBase I)) →ₐ[K] K =>
        p.comp (coordinate G I)) :=
  bijective_coordinates (coordinate G I) (affine_points_bijective G I)

/-- Multiplication identifies the Levi product with the standard parabolic as a variety. -/
instance parabolicMultiplication_isIso (I : Set G.rootBase.support) :
    IsIso (parabolicMultiplication G I) := by
  have hd := affineMulTangent_injective (factorL G I) (factorR G I)
    (CommHopfAlgCat.quotientMapOfLe_surjective G.coordinateAlgebra.obj (pIdeal_le_levi G I))
    (CommHopfAlgCat.quotientMapOfLe_surjective G.coordinateAlgebra.obj (pIdeal_le_root G I))
    (factorTangents_disjoint G I)
  have hspec : IsIso (Spec.map (CommRingCat.ofHom (coordinate G I).toRingHom)) :=
    affineMulMap_isIso (factorL G I) (factorR G I) hd (coordinate_points_bijective G I)
  have : IsIso ((Over.forget (Spec (CommRingCat.of K))).map
      (coordinateHom G I)) := by
    change IsIso (Spec.map (CommRingCat.ofHom (coordinate G I).toRingHom))
    exact hspec
  have hOver : IsIso (coordinateHom G I) :=
    isIso_of_reflects_iso (coordinateHom G I)
      (Over.forget (Spec (CommRingCat.of K)))
  exact IsIso.of_isIso_fac_left (hh := hOver) (tensorIso_comp G I)

/-- The Levi decomposition isomorphism has the group multiplication morphism as its forward map. -/
def parabolicLeviIso (I : Set G.rootBase.support) :
    (parabolicLeviProduct G I).toOver ≅ (standardParabolicVariety G I).toOver :=
  asIso (parabolicMultiplication G I)

end SchubertGeometry
