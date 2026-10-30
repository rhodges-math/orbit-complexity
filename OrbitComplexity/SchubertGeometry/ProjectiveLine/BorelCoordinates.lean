import OrbitComplexity.ReductiveGroups.Roots.Parabolic.Singleton
import OrbitComplexity.GroupActions.Varieties.RootLine
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionBorelVariety
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSimpleRoots
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTangent

/-! # Torus and additive coordinates on a singleton Levi Borel -/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private instance additiveIntegral : IsIntegral (additiveVariety K).scheme := by
  let : IsDomain (SymmetricAlgebra K K) := (gaPolynomialEquiv K).injective.isDomain
  exact (affine_isIntegral_iff (CommRingCat.of (SymmetricAlgebra K K))).mpr inferInstance

private theorem rootMap_kills (i : G.rootBase.support)
    (hR : IsPositiveRootClosed G.rootBase {i.val}) :
    ∀ a ∈ G.rootSubsetIdeal {i.val} hR, gaAffineGroupTangent (G.simpleRootMap i) a = 0 := by
  apply (tangent_mem_hopfQuotient_iff _ _).mp
  change gaAffineGroupTangent (G.simpleRootMap i) ∈
    (hopfTangentImage (G.rootSubsetIdeal {i.val} hR)).toSubmodule
  rw [G.singletonRootTangent i.val (G.rootBase.isPos_of_mem_support i.property) hR]
  exact G.simpleRootMap_tangent_mem i

private def simpleRootSetIso (i : G.rootBase.support) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (he : R = {i.val}) :
    (additiveVariety K).toOver ≅ (rootSubsetVariety G R hR).toOver := by
  subst R
  exact rootLineIso G i.val (G.rootBase.isPos_of_mem_support i.property) hR
    (G.simpleRootMap i) (rootMap_kills G i hR) (G.simpleRootMap_tangent_ne_zero i)

private theorem simpleRootSetIso_comp (i : G.rootBase.support) (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (he : R = {i.val}) :
    (simpleRootSetIso G i R hR he).hom ≫ rootSubsetInclusion G R hR =
      gaMorphism G (G.simpleRootMap i) := by
  subst R
  exact rootLineIso_hom_comp G i.val (G.rootBase.isPos_of_mem_support i.property) hR
    (G.simpleRootMap i) (rootMap_kills G i hR) (G.simpleRootMap_tangent_ne_zero i)

@[irreducible] private def rootIso (i : G.rootBase.support) :
    (additiveVariety K).toOver ≅
      (rootSubsetVariety G (leviPositiveRoots G.rootBase {i})
        (LeviRootSpan.isPositiveRootClosed G.rootBase {i})).toOver :=
  simpleRootSetIso G i _ _ (leviPositiveRoots_singleton G.rootBase i)

/-- Multiplication identifies the torus and the selected additive root with the singleton Borel. -/
def simpleBorelCoordinates (i : G.rootBase.support) :
    (Variety.productVariety (torusVariety G) (additiveVariety K)).toOver ≅
      (leviBorelVariety G {i}).toOver :=
  tensorIso (Iso.refl (torusVariety G).toOver) (rootIso G i) ≪≫ leviBorelProductIso G {i}

private theorem tensor_mul_comp {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B A' B' H D : C} [MonObj H] [MonObj D]
    (f : A' ⟶ A) (g : B' ⟶ B) (t : A ⟶ H) (v : B ⟶ H)
    (h : H ⟶ D) [IsMonHom h] :
    (f ⊗ₘ g) ≫ ((fst A B ≫ t) * (snd A B ≫ v)) ≫ h =
      (fst A' B' ≫ f ≫ t ≫ h) * (snd A' B' ≫ g ≫ v ≫ h) := by
  rw [MonObj.mul_comp, MonObj.comp_mul]
  simp only [← Category.assoc, tensorHom_fst, tensorHom_snd]

/-- The singleton Borel coordinate map is torus times the specified additive root map. -/
theorem simpleBorelCoordinates_comp (i : G.rootBase.support) :
    (simpleBorelCoordinates G i).hom ≫ leviBorelInclusion G {i} =
      (fst _ _ ≫ torusInclusion G) * (snd _ _ ≫ gaMorphism G (G.simpleRootMap i)) := by
  have hm := tensor_mul_comp (𝟙 (torusVariety G).toOver) (rootIso G i).hom
    (torusLeviBorelInclusion G {i}) (leviRootBorelInclusion G {i})
    (leviBorelInclusion G {i})
  have hr : (rootIso G i).hom ≫ rootSubsetInclusion G _ _ =
      gaMorphism G (G.simpleRootMap i) := by
    rw [rootIso]
    exact simpleRootSetIso_comp G i _ _ (leviPositiveRoots_singleton G.rootBase i)
  simpa only [simpleBorelCoordinates, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    leviBorelProductIso, asIso_hom, leviBorelMultiplication, Category.assoc, Category.id_comp,
    torusLeviBorelInclusion_comp, leviRootBorelInclusion_comp, hr] using hm

end SchubertGeometry
