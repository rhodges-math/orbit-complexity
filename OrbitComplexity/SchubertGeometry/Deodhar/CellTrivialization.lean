import OrbitComplexity.SchubertGeometry.Deodhar.RootParameter
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-! # Additive-line trivializations of cell projections

The fixed root parameter identifies the last factor in the root-product cell chart with
the additive line. The cell projection becomes its first projection.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

private abbrev precedingAlgebra := G.rootSubsetAlgebra
  (leftRootInversionIndices G.rootBase w)
  (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

private theorem gaProductDomain : IsDomain (precedingAlgebra G w ⊗[K] SymmetricAlgebra K K) :=
  GroupActions.isDomain_tensorProduct
attribute [local instance] gaProductDomain

private theorem gaProductFiniteType :
    Algebra.FiniteType K (precedingAlgebra G w ⊗[K] SymmetricAlgebra K K) :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K (precedingAlgebra G w))
    (inferInstance : Algebra.FiniteType (precedingAlgebra G w)
      (precedingAlgebra G w ⊗[K] SymmetricAlgebra K K))
attribute [local instance] gaProductFiniteType

/-- The affine product of the preceding inversion subgroup and the additive line. -/
def rankOneGaProductVariety : GroupActions.Variety K :=
  GroupActions.affineVariety K (precedingAlgebra G w ⊗[K] SymmetricAlgebra K K)

/-- The fixed additive parameter identifies the affine product with the root product. -/
def rankOneGaProductIso : (rankOneGaProductVariety G w).toOver ≅
    (rankOneProductVariety G w i hw).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (Algebra.TensorProduct.congr
    (AlgEquiv.refl : precedingAlgebra G w ≃ₐ[K] precedingAlgebra G w)
      (rankOneGaCoordinates G w i hw))).op

/-- The preceding inversion subgroup times the additive line is the extended Schubert cell. -/
def rankOneGaCellIso : (rankOneGaProductVariety G w).toOver ≅
    (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  rankOneGaProductIso G w i hw ≪≫ rankOneCellIso G w i hw

/-- The first projection of the additive-line product. -/
def rankOneGaFirst : (rankOneGaProductVariety G w).toOver ⟶ (schubertUnipotent G w).toOver :=
  GroupActions.affineMorphism (Algebra.TensorProduct.includeLeft :
    precedingAlgebra G w →ₐ[K] precedingAlgebra G w ⊗[K] SymmetricAlgebra K K)

/-- The additive root-parameter product isomorphism preserves the first projection. -/
theorem rankOneGaProductIso_first :
    (rankOneGaProductIso G w i hw).hom ≫ rankOneFirst G w i hw = rankOneGaFirst G w := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr
      (AlgEquiv.refl : precedingAlgebra G w ≃ₐ[K] precedingAlgebra G w)
        (rankOneGaCoordinates G w i hw)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeft.toRingHom) =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeft.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  simp

/-- The cell projection is the first projection under the additive-line trivialization. -/
theorem rankOneGaCellIso_projection :
    (rankOneGaCellIso G w i hw).hom ≫ rankOneCellProjection G w i hw =
      rankOneGaFirst G w ≫ (schubertCellIso G w).hom := by
  dsimp only [rankOneGaCellIso, Iso.trans_hom]
  rw [Category.assoc, rankOneCellProjection_comp, ← Category.assoc,
    rankOneGaProductIso_first]

/-- Rational points of the additive-line product are pairs of points of its factors. -/
def rankOneGaProductPointsEquiv : (rankOneGaProductVariety G w).points ≃
    (schubertUnipotent G w).points × (GroupActions.additiveVariety K).points :=
  GroupActions.affineProductPointsEquiv K (precedingAlgebra G w) (SymmetricAlgebra K K)

/-- The product chart keeps the first point and applies the fixed root-line parameter second. -/
theorem rankOneGaProductIso_points (x : (rankOneGaProductVariety G w).points) :
    GroupActions.rootProductPointsEquiv G _ _
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
      (rankOneRoot_closed G w i hw)
      (GroupActions.Variety.mapPoints (rankOneGaProductIso G w i hw).hom x) =
        ((rankOneGaProductPointsEquiv G w x).1,
          GroupActions.Variety.mapPoints (rankOneGaIso G w i hw).hom
            (rankOneGaProductPointsEquiv G w x).2) := by
  let A := precedingAlgebra G w
  let B := G.rootSubsetAlgebra (rankOneRootSet G w i) (rankOneRoot_closed G w i hw)
  let : IsDomain (A ⊗[K] B) := GroupActions.isDomain_tensorProduct
  let : Algebra.FiniteType K (A ⊗[K] B) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K A)
    (inferInstance : Algebra.FiniteType A (A ⊗[K] B))
  let C : A ⊗[K] B ≃ₐ[K] A ⊗[K] SymmetricAlgebra K K :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[K] A) (rankOneGaCoordinates G w i hw)
  obtain ⟨p, rfl⟩ := GroupActions.affinePointsEquiv.surjective x
  let p₁ : A →ₐ[K] K := p.comp Algebra.TensorProduct.includeLeft
  let p₂ : SymmetricAlgebra K K →ₐ[K] K := p.comp Algebra.TensorProduct.includeRight
  have hm : GroupActions.Variety.mapPoints (rankOneGaProductIso G w i hw).hom
      (GroupActions.affinePointsEquiv p) =
        GroupActions.affinePointsEquiv (p.comp C.toAlgHom) :=
    GroupActions.affineMorphism_points C.toAlgHom p
  have hm₂ : GroupActions.Variety.mapPoints (rankOneGaIso G w i hw).hom
      (GroupActions.affinePointsEquiv p₂) = GroupActions.affinePointsEquiv
        (p₂.comp (rankOneGaCoordinates G w i hw).toAlgHom) :=
    GroupActions.affineMorphism_points (rankOneGaCoordinates G w i hw).toAlgHom p₂
  have hl : (p.comp C.toAlgHom).comp Algebra.TensorProduct.includeLeft = p₁ := by
    ext a
    simp [C, p₁]
  have hr : (p.comp C.toAlgHom).comp Algebra.TensorProduct.includeRight =
      p₂.comp (rankOneGaCoordinates G w i hw).toAlgHom := by
    ext b
    simp [C, p₂]
  rw [hm]
  have he₁ : GroupActions.rootProductPointsEquiv G _ _
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
      (rankOneRoot_closed G w i hw) (GroupActions.affinePointsEquiv (p.comp C.toAlgHom)) =
        (GroupActions.affinePointsEquiv ((p.comp C.toAlgHom).comp
          Algebra.TensorProduct.includeLeft), GroupActions.affinePointsEquiv
            ((p.comp C.toAlgHom).comp Algebra.TensorProduct.includeRight)) := by
    change (Equiv.prodCongr GroupActions.affinePointsEquiv GroupActions.affinePointsEquiv)
      ((GroupActions.tensorAlgebraPointsEquiv K A B)
        (GroupActions.affinePointsEquiv.symm
          (GroupActions.affinePointsEquiv (p.comp C.toAlgHom)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have he₂ : rankOneGaProductPointsEquiv G w (GroupActions.affinePointsEquiv p) =
      (GroupActions.affinePointsEquiv p₁, GroupActions.affinePointsEquiv p₂) := by
    change (Equiv.prodCongr GroupActions.affinePointsEquiv GroupActions.affinePointsEquiv)
      ((GroupActions.tensorAlgebraPointsEquiv K A (SymmetricAlgebra K K))
        (GroupActions.affinePointsEquiv.symm (GroupActions.affinePointsEquiv p))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [he₁, hl, hr, he₂, hm₂]
  rfl
end
end SchubertGeometry
