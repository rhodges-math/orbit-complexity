import OrbitComplexity.FrobeniusSplitting.Normality.Models.ScalarImageBaseChangeData

/-! # Flat scalar images as coefficient base changes -/

open scoped TensorProduct
noncomputable section
namespace FrobeniusSplitting

private theorem scalarImage_injective {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Module.Flat S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (scalarImageHom (R := R) e) := by
  apply e.injective.comp
  change Function.Injective (((Algebra.ofId R K).restrictScalars S).toLinearMap.rTensor M)
  exact Module.Flat.rTensor_preserves_injective_linearMap _ hi

/-- The intrinsic model of a flat chosen algebra is its coefficient base change. -/
theorem scalarImage_baseChange {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Module.Flat S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    scalarImageBaseChangeSpec (R := R) e := by
  let q := scalarImageHom (R := R) e
  let d : R ⊗[S] M ≃ₐ[R] q.range :=
    AlgEquiv.ofBijective q.rangeRestrict
      ⟨fun _ _ h ↦ scalarImage_injective e hi (congrArg Subtype.val h),
        q.rangeRestrict_surjective⟩
  exact ⟨d, fun _ ↦ rfl⟩

end FrobeniusSplitting
