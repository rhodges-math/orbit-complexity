import OrbitComplexity.FrobeniusSplitting.Normality.Products.AffineProductSmooth
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedCoverSmooth

/-! # Smooth tensor coordinates of paired BSDH covers

The affine Borel-product spectrum is compared with the Borel-product
scheme. Restriction to an affine open of the paired source then gives
the smooth coordinate tensor needed for pointed coefficient models.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- An affine open of the raw paired source has a smooth tensor product
with the Borel-product coordinate algebra, by flag transversality. -/
theorem pairedBSDH_tensor_smooth (a b : List G.rootBase.support)
    (A : Type u) [CommRing A] [Algebra K A]
    (j : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶
      pairedBSDHSource G a b) [IsOpenImmersion j.left] :
    Algebra.Smooth K (A ⊗[K] (G.borelAlgebra ⊗[K] G.oppositeBorelAlgebra)) := by
  let B := G.borelAlgebra ⊗[K] G.oppositeBorelAlgebra
  let H : Over (Spec (CommRingCat.of K)) :=
    (borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver
  let Hb : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  let e : Hb ≅ H := Over.isoMk
    (pullbackSpecIso K G.borelAlgebra G.oppositeBorelAlgebra).symm (by
      change (pullbackSpecIso K G.borelAlgebra G.oppositeBorelAlgebra).inv ≫
        (pullback.fst _ _ ≫ Spec.map
          (CommRingCat.ofHom (algebraMap K G.borelAlgebra))) = _
      rw [← Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      rfl)
  have : Smooth (H ⊗ pairedBSDHSource G a b).hom := pairedBSDHCover_smooth G a b
  let E := e ⊗ᵢ Iso.refl (pairedBSDHSource G a b)
  have : Smooth (Hb ⊗ pairedBSDHSource G a b).hom := by
    rw [← E.hom.w]
    infer_instance
  exact FrobeniusSplitting.smooth_tensor_of_open_product K A B
    (pairedBSDHSource G a b) j

end
end SchubertGeometry
