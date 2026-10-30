import OrbitComplexity.SchubertGeometry.BSDH.Surjectivity
import OrbitComplexity.SchubertGeometry.Parabolics.SimpleIncidence
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Omitted BSDH steps and reduced Schubert images

The diagonal in the simple incidence correspondence gives an endpoint-preserving
closed section. Reduced-word endpoints have the ideals of their Schubert images.
-/

noncomputable section
namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem simple_bundle_section (i : G.rootBase.support) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    ∃ j : (flagVariety G).scheme ⟶ flagBundleScheme G Y,
      j ≫ flagBundleProjection G Y = 𝟙 _ ∧
        j ≫ flagBundleMap G Y
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) = 𝟙 _ := by
  dsimp only
  obtain ⟨e, he₁, he₂⟩ := simpleSchubert_incidence G i
  let p := (partialFlagMorphism G {i}).left
  let d : (flagVariety G).scheme ⟶ pullback p p :=
    pullback.lift (𝟙 _) (𝟙 _) (by simp)
  refine ⟨d ≫ e.inv, ?_, ?_⟩
  · rw [← he₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [← he₂]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _

/-- Omitting the last simple step gives a closed section preserving the flag endpoint. -/
theorem bsdh_omitted_section (word : List G.rootBase.support) (i : G.rootBase.support) :
    ∃ d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i]),
      IsClosedImmersion d ∧ d ≫ bsdhAppendFst G word i = 𝟙 _ ∧
        d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let π := flagBundleProjection G Y
  let τ := flagBundleMap G Y
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
  obtain ⟨j, hjπ, hjτ⟩ := simple_bundle_section G i
  have hjπ' : j ≫ π = 𝟙 _ := hjπ
  let q : bsdhScheme G word ⟶ pullback (bsdhMap G word) π :=
    pullback.lift (𝟙 _) (bsdhMap G word ≫ j) (by
      rw [Category.id_comp, Category.assoc, hjπ', Category.comp_id])
  let e := (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)
  let d := q ≫ e.inv
  have hdπ : d ≫ bsdhAppendFst G word i = 𝟙 _ := by
    change (q ≫ e.inv) ≫ (e.hom ≫ pullback.fst (bsdhMap G word) π) = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  have hdτ : d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word := by
    rw [← bsdhAppendIso_endpoint G word i]
    change (q ≫ e.inv) ≫ e.hom ≫ pullback.snd (bsdhMap G word) π ≫ τ = _
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    change q ≫ pullback.snd (bsdhMap G word) π ≫ τ = _
    rw [← Category.assoc, pullback.lift_snd, Category.assoc, hjτ, Category.comp_id]
  have : IsClosedImmersion (d ≫ bsdhAppendFst G word i) := by
    rw [hdπ]
    infer_instance
  exact ⟨d, IsClosedImmersion.of_comp d (bsdhAppendFst G word i), hdπ, hdτ⟩

private theorem kernel_vanishing_image {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
  calc
    f.ker = (⊥ : X.IdealSheafData).map f :=
      (Scheme.IdealSheafData.map_bot f).symm
    _ = (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)).map f := by
      rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
    _ = _ := by
      rw [Scheme.IdealSheafData.map_vanishingIdeal]
      congr 1
      congr 1
      exact Set.image_univ

private theorem endpoint_range (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    Set.range (bsdhMap G word) =
      Set.range (schubertInclusion G (simpleWeylWord G.rootBase word)).left := by
  rw [← bsdhSchubertMap_comp G word hred]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(bsdhSchubertMap G word hred).left x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (bsdhSchubertMap G word hred).left.surjective x
    exact ⟨y, rfl⟩

/-- The image ideal of a reduced-word endpoint is the ideal of its Schubert variety. -/
theorem bsdh_endpoint_ideal (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    (bsdhMap G word).ker =
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left.ker := by
  rw [kernel_vanishing_image (bsdhMap G word), endpoint_range G word hred]
  rw [schubertInclusion_range]
  have he : TopologicalSpace.Closeds.closure
      (closure (Set.range (schubertCellInclusion G
        (simpleWeylWord G.rootBase word)).left)) =
        schubertSupport G (simpleWeylWord G.rootBase word) := by
    apply SetLike.coe_injective
    exact closure_closure
  rw [he]
  change Scheme.IdealSheafData.vanishingIdeal
    (schubertSupport G (simpleWeylWord G.rootBase word)) =
      (Scheme.IdealSheafData.vanishingIdeal
        (schubertSupport G (simpleWeylWord G.rootBase word))).subschemeι.ker
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

end SchubertGeometry
