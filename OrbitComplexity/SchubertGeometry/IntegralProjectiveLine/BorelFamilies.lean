import OrbitComplexity.SchubertGeometry.ProjectiveLine.RootTranslations
import OrbitComplexity.SchubertGeometry.ProjectiveLine.TorusAutomorphisms
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Automorphisms
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import Mathlib.Tactic.CategoryTheory.Reassoc
import OrbitComplexity.SchubertGeometry.ProjectiveLine.BorelCoordinatePoints
import OrbitComplexity.SchubertGeometry.Levi.BorelInclusion
import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.ProjectiveConnected
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineSpecialization
import OrbitComplexity.GroupActions.Actions.ActionFamilies

noncomputable section
namespace SchubertGeometry
open GroupActions CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  [IsReduced A] [IsReduced B] [IsReduced (A ⊗[K] B)]
  [Algebra.FiniteType K A] [Algebra.FiniteType K B] [Algebra.FiniteType K (A ⊗[K] B)]

private theorem tensorFst_value (f : A ⊗[K] B →ₐ[K] K) :
    Variety.mapPoints ((affineTensorIso K A B).hom ≫ fst _ _)
      ((affineVarietyPointsEquiv K (A ⊗[K] B)).symm f) =
        (affineVarietyPointsEquiv K A).symm (f.comp Algebra.TensorProduct.includeLeft) := by
  rw [affineTensorIso_fst, affineMorphism_points]

private theorem tensorSnd_value (f : A ⊗[K] B →ₐ[K] K) :
    Variety.mapPoints ((affineTensorIso K A B).hom ≫ snd _ _)
      ((affineVarietyPointsEquiv K (A ⊗[K] B)).symm f) =
        (affineVarietyPointsEquiv K B).symm (f.comp Algebra.TensorProduct.includeRight) := by
  rw [affineTensorIso_snd, affineMorphism_points]

end SchubertGeometry
end

/-! # Coefficient algebras for a singleton Levi Borel -/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The torus and additive coordinates of a singleton Levi Borel. -/
abbrev simpleBorelCoefficientAlgebra := G.torusAlgebra ⊗[K] SymmetricAlgebra K K

private instance torusDomain : IsDomain G.torusAlgebra :=
  (affine_isIntegral_iff (CommRingCat.of G.torusAlgebra)).mp
    (inferInstanceAs (IsIntegral (torusVariety G).scheme))

private instance additiveDomain : IsDomain (SymmetricAlgebra K K) :=
  (gaPolynomialEquiv K).injective.isDomain

/-- The singleton Levi-Borel coefficient algebra is an integral domain. -/
instance simpleBorelCoefficientDomain : IsDomain (simpleBorelCoefficientAlgebra G) :=
  isDomain_tensorProduct

/-- The singleton Levi-Borel coefficient algebra has finite type over its field. -/
instance simpleBorelCoefficientFinite : Algebra.FiniteType K (simpleBorelCoefficientAlgebra G) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K G.torusAlgebra)
    (inferInstance : Algebra.FiniteType G.torusAlgebra (simpleBorelCoefficientAlgebra G))

/-- Tensor coordinates identify the singleton Levi Borel with torus times the chosen root line. -/
def simpleBorelTensorIso (i : G.rootBase.support) :
    (affineVariety K (simpleBorelCoefficientAlgebra G)).toOver ≅ (leviBorelVariety G {i}).toOver :=
  affineTensorIso K G.torusAlgebra (SymmetricAlgebra K K) ≪≫ simpleBorelCoordinates G i

private def characterUnit (i : G.rootBase.support) :
    (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)))ˣ where
  val := MonoidAlgebra.single (G.rootCharacter i.val) 1
  inv := MonoidAlgebra.single (G.rootCharacter i.val)⁻¹ 1
  val_inv := by simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
  inv_val := by simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]

/-- The simple root character is a unit of the singleton Levi-Borel coordinate algebra. -/
def simpleRootCoefficient (i : G.rootBase.support) : (simpleBorelCoefficientAlgebra G)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft :
    G.torusAlgebra →ₐ[K] simpleBorelCoefficientAlgebra G).toMonoidHom
      (Units.map (torusCoordinateEquiv G).symm.toMonoidHom (characterUnit G i))

/-- The additive parameter in the singleton Levi-Borel coordinate algebra. -/
def simpleRootParameter : simpleBorelCoefficientAlgebra G :=
  Algebra.TensorProduct.includeRight (R := K) (A := G.torusAlgebra)
    (SymmetricAlgebra.ι K K 1)


end SchubertGeometry
end

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private def groupFamily (i : G.rootBase.support) :
    (affineVariety K (simpleBorelCoefficientAlgebra G)).toOver ⊗
        (projectiveVariety K (ULift.{u} (Fin 2))).toOver ⟶
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  ((simpleBorelTensorIso G i).hom ⊗ₘ (simpleSchubertIso G i).inv) ≫
    (leviBorelLeviInclusion G {i} ▷
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
    ModObj.smul (M := (leviVariety G {i}).toOver)
      (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
    (simpleSchubertIso G i).hom

private def matrixFamily (i : G.rootBase.support) :
    (affineVariety K (simpleBorelCoefficientAlgebra G)).toOver ⊗
        (projectiveVariety K (ULift.{u} (Fin 2))).toOver ⟶
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  projectiveAffineFamily (algebraMap K (simpleBorelCoefficientAlgebra G))
    (simpleRootCoefficient G i)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)


end SchubertGeometry
end

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem additivePoint_value (f : SymmetricAlgebra K K →ₐ[K] K) :
    (affineVarietyPointsEquiv K (SymmetricAlgebra K K)).symm f =
      additivePointsEquiv K (f (SymmetricAlgebra.ι K K 1)) := by
  have h : WithConv.toConv f = (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
      (Multiplicative.ofAdd (f (SymmetricAlgebra.ι K K 1))) := by
    apply (AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).injective
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd (AdditiveGroup.toAdd_gaPointsMulEquiv (WithConv.toConv f))
  exact congrArg (affineGroupPointsMulEquiv K (SymmetricAlgebra K K)) h

private def torusPointAlg (f : G.torusAlgebra →ₐ[K] K) : (torusVariety G).points :=
  (affineVarietyPointsEquiv K G.torusAlgebra).symm f

private def splitPointAlg (f : G.torusAlgebra →ₐ[K] K) :
    WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K) :=
  WithConv.toConv (f.comp (torusCoordinateEquiv G).symm.toAlgHom)

omit [IsAlgClosed K] [CharZero K] in
private theorem splitPointAlg_map (f : G.torusAlgebra →ₐ[K] K) :
    AlgHom.mapDomain G.torusSplit (splitPointAlg G f) =
      (torusPointsMulEquiv G (torusPointAlg G f) : G.points) := by
  rw [torusPointsMulEquiv_coe]
  have hf : affinePointsEquiv.symm (torusPointAlg G f) = f :=
    (affinePointsEquiv (K := K) (R := G.torusAlgebra)).symm_apply_apply f
  ext a
  rw [AlgHom.mapDomain_apply_apply, CommHopfAlgCat.quotientPointsHom_apply_apply]
  have h : (torusCoordinateEquiv G).symm (G.torusSplit a) =
      Ideal.Quotient.mk G.torusIdeal.toIdeal a := by
    rw [← torusCoordinateEquiv_mk]
    exact (torusCoordinateEquiv G).symm_apply_apply _
  calc
    _ = f ((torusCoordinateEquiv G).symm (G.torusSplit a)) := rfl
    _ = f (Ideal.Quotient.mk G.torusIdeal.toIdeal a) := congrArg f h
    _ = _ := (congrArg (fun q : G.torusAlgebra →ₐ[K] K =>
      q (Ideal.Quotient.mk G.torusIdeal.toIdeal a)) hf).symm

private def coefficientPoint (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) :
    (affineVariety K (simpleBorelCoefficientAlgebra G)).points :=
  (affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f

private def borelCoefficientPoint (i : G.rootBase.support)
    (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) : (leviBorelVariety G {i}).points :=
  Variety.mapPoints (simpleBorelTensorIso G i).hom (coefficientPoint G f)

private theorem tensorBorelIso_point_factors (i : G.rootBase.support)
    (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) :
    (leviBorelPointsMulEquiv G {i} (borelCoefficientPoint G i f) : G.points) =
      AlgHom.mapDomain G.torusSplit
        (splitPointAlg G (f.comp Algebra.TensorProduct.includeLeft)) *
      gaParameterPoint (G.simpleRootMap i) (f (simpleRootParameter G)) := by
  let p := Variety.mapPoints
    (X := affineVariety K (simpleBorelCoefficientAlgebra G))
    (Y := Variety.productVariety (torusVariety G) (additiveVariety K))
    (affineTensorIso K G.torusAlgebra (SymmetricAlgebra K K)).hom
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f)
  have h := simpleBorelCoordinates_points G i p
  have ht : Variety.mapPoints
      (X := Variety.productVariety (torusVariety G) (additiveVariety K))
      (Y := torusVariety G) (fst _ _) p =
        torusPointAlg G (f.comp Algebra.TensorProduct.includeLeft) := by
    exact (Variety.mapPoints_comp (X := affineVariety K (simpleBorelCoefficientAlgebra G))
      (Y := Variety.productVariety (torusVariety G) (additiveVariety K)) (Z := torusVariety G)
      (affineTensorIso K G.torusAlgebra (SymmetricAlgebra K K)).hom (fst _ _)
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f)).symm.trans
        (tensorFst_value f)
  have ha : Variety.mapPoints
      (X := Variety.productVariety (torusVariety G) (additiveVariety K))
      (Y := additiveVariety K) (snd _ _) p = additivePointsEquiv K (f (simpleRootParameter G)) := by
    exact (Variety.mapPoints_comp (X := affineVariety K (simpleBorelCoefficientAlgebra G))
      (Y := Variety.productVariety (torusVariety G) (additiveVariety K)) (Z := additiveVariety K)
      (affineTensorIso K G.torusAlgebra (SymmetricAlgebra K K)).hom (snd _ _)
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f)).symm.trans
        ((tensorSnd_value f).trans
          (additivePoint_value (f.comp Algebra.TensorProduct.includeRight)))
  have hb : Variety.mapPoints (simpleBorelTensorIso G i).hom
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f) =
      Variety.mapPoints (simpleBorelCoordinates G i).hom p := by
    exact Variety.mapPoints_comp (X := affineVariety K (simpleBorelCoefficientAlgebra G))
      (Y := Variety.productVariety (torusVariety G) (additiveVariety K))
      (Z := leviBorelVariety G {i})
      (affineTensorIso K G.torusAlgebra (SymmetricAlgebra K K)).hom
      (simpleBorelCoordinates G i).hom
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f)
  change (leviBorelPointsMulEquiv G {i}
    (Variety.mapPoints (simpleBorelTensorIso G i).hom
      ((affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm f)) : G.points) = _
  rw [hb]
  have ht' : (torusPointsMulEquiv G (Variety.mapPoints (fst _ _) p) : G.points) =
      AlgHom.mapDomain G.torusSplit
        (splitPointAlg G (f.comp Algebra.TensorProduct.includeLeft)) :=
    (congrArg (fun t : (torusVariety G).points => (torusPointsMulEquiv G t : G.points))
      ht).trans (splitPointAlg_map G (f.comp Algebra.TensorProduct.includeLeft)).symm
  have ha' : gaParameterPoint (G.simpleRootMap i)
      ((additivePointsEquiv K).symm (Variety.mapPoints (snd _ _) p)) =
        gaParameterPoint (G.simpleRootMap i) (f (simpleRootParameter G)) :=
    congrArg (gaParameterPoint (G.simpleRootMap i))
      ((congrArg (additivePointsEquiv K).symm ha).trans
        ((additivePointsEquiv K).symm_apply_apply (f (simpleRootParameter G))))
  exact h.trans (congrArg₂ (fun x y : G.points => x * y) ht' ha')

private theorem rootCoefficient_value (i : G.rootBase.support)
    (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) :
    (Units.map f.toMonoidHom (simpleRootCoefficient G i) : K) =
      (splitPointAlg G (f.comp Algebra.TensorProduct.includeLeft)).ofConv
        (MonoidAlgebra.single (G.rootCharacter i.val) 1) := rfl


private def rootLeviPoint (i : G.rootBase.support) (a : K) : (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨gaParameterPoint (G.simpleRootMap i) a, G.simpleRootPoint_mem_levi {i} i (by simp) a⟩

private def splitLeviPoint (i : G.rootBase.support)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    (leviVariety G {i}).points :=
  (leviPointsMulEquiv G {i}).symm
    ⟨AlgHom.mapDomain G.torusSplit z, G.torus_le_leviPoints {i}
      (mapDomain_mem_torusPoints G.torusIdeal G.torusSplit G.split_surjective G.split_eq_zero z)⟩

private theorem coefficient_levi_factor (i : G.rootBase.support)
    (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) :
    Variety.mapPoints (leviBorelLeviInclusion G {i}) (borelCoefficientPoint G i f) =
      splitLeviPoint G i (splitPointAlg G (f.comp Algebra.TensorProduct.includeLeft)) *
        rootLeviPoint G i (f (simpleRootParameter G)) := by
  apply (leviPointsMulEquiv G {i}).injective
  apply Subtype.ext
  rw [leviBorelLeviInclusion_points]
  simpa only [map_mul, splitLeviPoint, rootLeviPoint, MulEquiv.apply_symm_apply,
    Subgroup.coe_mul] using tensorBorelIso_point_factors G i f

omit [IsAlgClosed K] [CharZero K] in
private theorem translations_iso {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] (e : X.toOver ≅ Y.toOver)
    {g h : H.points} {m n : Y.toOver ⟶ Y.toOver}
    (hg : Variety.translateMorphism H X g ≫ e.hom = e.hom ≫ m)
    (hh : Variety.translateMorphism H X h ≫ e.hom = e.hom ≫ n) :
    Variety.translateMorphism H X (g * h) ≫ e.hom = e.hom ≫ n ≫ m := by
  rw [← Variety.translateMorphism_comp H X h g, Category.assoc, hg,
    ← Category.assoc, hh, Category.assoc]

private def translationOver (a : K) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ≅
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  Over.isoMk (projectiveLineTranslationIso a) (projectiveLineTranslation_base a)

private def scalingOver (c : Kˣ) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ≅
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  Over.isoMk (projectiveLineScalingIso c) (projectiveLineScaling_base c)

private theorem coefficient_action (i : G.rootBase.support)
    (f : simpleBorelCoefficientAlgebra G →ₐ[K] K) :
    Variety.translateMorphism (leviVariety G {i})
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
        (Variety.mapPoints (leviBorelLeviInclusion G {i}) (borelCoefficientPoint G i f)) ≫
        (simpleSchubertIso G i).hom =
      (simpleSchubertIso G i).hom ≫
        (translationOver (f (simpleRootParameter G))).hom ≫
        (scalingOver (Units.map f.toMonoidHom (simpleRootCoefficient G i))).hom := by
  obtain ⟨c, hc, ht⟩ := simpleSchubertIso_torus G i
    (splitPointAlg G (f.comp Algebra.TensorProduct.includeLeft))
  have hc' : c = Units.map f.toMonoidHom (simpleRootCoefficient G i) :=
    Units.ext (hc.trans (rootCoefficient_value G i f).symm)
  subst c
  have hp := translations_iso (H := leviVariety G {i}) (simpleSchubertIso G i)
    ht (simpleSchubertIso_ga G i (f (simpleRootParameter G)))
  have hf := congrArg (fun q : (leviVariety G {i}).points =>
    Variety.translateMorphism (leviVariety G {i})
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q ≫
        (simpleSchubertIso G i).hom) (coefficient_levi_factor G i f)
  exact hf.trans hp


private instance coefficientIntegral :
    IsIntegral (affineVariety K (simpleBorelCoefficientAlgebra G)).scheme := by
  change IsIntegral (Spec (CommRingCat.of (simpleBorelCoefficientAlgebra G)))
  infer_instance

private instance projectiveIntegral :
    IsIntegral (projectiveVariety K (ULift.{u} (Fin 2))).scheme := by
  change IsIntegral (projectiveScheme K (ULift.{u} (Fin 2)))
  infer_instance

private theorem groupFamily_eq_matrix (i : G.rootBase.support) :
    groupFamily G i = matrixFamily G i := by
  apply GroupActions.Variety.actionFamily_eq_of_sections
    (affineVariety K (simpleBorelCoefficientAlgebra G)) (leviBorelVariety G {i})
    (leviVariety G {i})
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectiveVariety K (ULift.{u} (Fin 2)))
    (simpleBorelTensorIso G i).hom (leviBorelLeviInclusion G {i}) (simpleSchubertIso G i)
  intro a
  obtain ⟨f, rfl⟩ :=
    (affineVarietyPointsEquiv K (simpleBorelCoefficientAlgebra G)).symm.surjective a
  have hp := Variety.mapPoints_comp (simpleBorelTensorIso G i).hom
    (leviBorelLeviInclusion G {i}) (coefficientPoint G f)
  have hpoint := congrArg (fun q : (leviVariety G {i}).points =>
    Variety.translateMorphism (leviVariety G {i})
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q ≫
        (simpleSchubertIso G i).hom) hp
  have ht := congrArg (fun q => (simpleSchubertIso G i).inv ≫ q)
    (hpoint.trans (coefficient_action G i f))
  simp only [Iso.inv_hom_id_assoc] at ht
  have hm : Variety.pointSection (affineVariety K (simpleBorelCoefficientAlgebra G))
        (projectiveVariety K (ULift.{u} (Fin 2))) (coefficientPoint G f) ≫ matrixFamily G i =
      (translationOver (f (simpleRootParameter G))).hom ≫
        (scalingOver (Units.map f.toMonoidHom (simpleRootCoefficient G i))).hom := by
    apply Over.OverMorphism.ext
    exact projectiveAffineFamily_specialize f (simpleRootCoefficient G i) (simpleRootParameter G)
  exact ht.trans hm.symm


/-- The singleton Levi-Borel action is its regular affine projective-line family. -/
theorem simpleLeviBorel_affine_family (i : G.rootBase.support) :
    (((simpleBorelTensorIso G i).hom ⊗ₘ (simpleSchubertIso G i).inv) ≫
      (leviBorelLeviInclusion G {i} ▷
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      ModObj.smul (M := (leviVariety G {i}).toOver)
        (X := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫
      (simpleSchubertIso G i).hom) =
    projectiveAffineFamily (algebraMap K (simpleBorelCoefficientAlgebra G))
      (simpleRootCoefficient G i)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G) :=
  groupFamily_eq_matrix G i

end SchubertGeometry
end
