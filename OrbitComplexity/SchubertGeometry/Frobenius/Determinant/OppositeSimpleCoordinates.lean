import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositeRootProduct
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# A specified additive coordinate on the opposite root product

The simple inversion factor is parametrized by the chosen simple-root map.
The resulting product chart is an isomorphism onto the opposite unipotent
group and agrees with multiplication followed by longest-Weyl conjugation.
-/

open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.DeterminantSection

noncomputable section

universe u

open private simpleElement simpleNoninversions simpleInversions
  simple_noninversions_closed simple_inversions_closed
  positiveProductIso simple_root_partition simple_root_disjoint from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositeRootProduct

open private GroupActions.coordinateReduced from
  OrbitComplexity.GroupActions.Varieties.ReductiveVariety
open private GroupActions.rootProductDomain GroupActions.rootProductFiniteType from
  OrbitComplexity.GroupActions.Varieties.RootSubgroupProduct

attribute [local instance] GroupActions.coordinateReduced
  GroupActions.rootProductDomain GroupActions.rootProductFiniteType

private theorem hopfSpec_map_hom {R : Type u} [CommRing R]
    {A B : CommHopfAlgCat.{u} R} (f : A ⟶ B) :
    ((hopfSpec (CommRingCat.of R)).map f.op).hom.hom =
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f.hom.toAlgHom).op := rfl

private theorem multiplication_congr {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {A B H : C} [MonObj H]
    (t t' : A ⟶ H) (v v' : B ⟶ H) (ht : t = t') (hv : v = v') :
    (fst A B ≫ t) * (snd A B ≫ v) =
      (fst A B ≫ t') * (snd A B ≫ v') := by
  rw [ht, hv]

private theorem product_change_comp {C : Type*} [Category C]
    {A B X Y Z : C} (d : A ≅ B) (e : X ≅ B) (q : X ≅ Y)
    (j : Y ⟶ Z) (m : B ⟶ Z) (hq : q.hom ≫ j = e.hom ≫ m) :
    (d ≪≫ e.symm ≪≫ q).hom ≫ j = d.hom ≫ m := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hq, ← Category.assoc e.inv e.hom m, e.inv_hom_id, Category.id_comp]

private theorem tensor_mul_comp {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {A B A' B' H : C} [MonObj H]
    (f : A' ⟶ A) (g : B' ⟶ B) (t : A ⟶ H) (v : B ⟶ H) :
    (f ⊗ₘ g) ≫ ((fst A B ≫ t) * (snd A B ≫ v)) =
      (fst A' B' ≫ f ≫ t) * (snd A' B' ≫ g ≫ v) := by
  rw [MonObj.comp_mul]
  simp only [← Category.assoc, tensorHom_fst, tensorHom_snd]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

private def rootQuotient (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    G.coordinateAlgebra →ₐ[K] G.rootSubsetAlgebra R hR :=
  Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal

private theorem root_inclusion_affine (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    rootSubsetInclusion G R hR =
      affineMorphism (rootQuotient G R hR) :=
  hopfSpec_map_hom (CommHopfAlgCat.mkQuotient
    (CommHopfAlgCat.of K G.coordinateAlgebra) (G.rootSubsetIdeal R hR))

private def complementVariety (i : G.rootBase.support) : Variety K :=
  rootSubsetVariety G (simpleNoninversions G i) (simple_noninversions_closed G i)

private def inversionVariety (i : G.rootBase.support) : Variety K :=
  rootSubsetVariety G (simpleInversions G i) (simple_inversions_closed G i)

private def complementInclusion (i : G.rootBase.support) :
    (complementVariety G i).toOver ⟶ (reductiveVariety G).toOver :=
  rootSubsetInclusion G (simpleNoninversions G i) (simple_noninversions_closed G i)

private def inversionInclusion (i : G.rootBase.support) :
    (inversionVariety G i).toOver ⟶ (reductiveVariety G).toOver :=
  rootSubsetInclusion G (simpleInversions G i) (simple_inversions_closed G i)

private def rootMultiplier (i : G.rootBase.support) :
    (complementVariety G i).toOver ⊗ (inversionVariety G i).toOver ⟶
      (reductiveVariety G).toOver :=
  (fst _ _ ≫ complementInclusion G i) * (snd _ _ ≫ inversionInclusion G i)

private def productTensorIso (i : G.rootBase.support) :
    (oppositeRootProduct G i).toOver ≅
      (complementVariety G i).toOver ⊗ (inversionVariety G i).toOver :=
  affineTensorIso K
    (G.rootSubsetAlgebra (simpleNoninversions G i) (simple_noninversions_closed G i))
    (G.rootSubsetAlgebra (simpleInversions G i) (simple_inversions_closed G i))

private theorem positive_product_ambient (i : G.rootBase.support) :
    (positiveProductIso G i).hom ≫ rootSubsetInclusion G {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase) =
        (productTensorIso G i).hom ≫ rootMultiplier G i := by
  have hraw := rootProductIso_hom_comp G {r | G.rootBase.IsPos r}
    (simpleNoninversions G i) (simpleInversions G i)
    (isPositiveRootClosed_isPos G.rootBase)
    (simple_noninversions_closed G i) (simple_inversions_closed G i)
    (simple_root_partition G i) (simple_root_disjoint G i)
  have hmul := affineTensorIso_mul
    (rootQuotient G (simpleNoninversions G i) (simple_noninversions_closed G i))
    (rootQuotient G (simpleInversions G i) (simple_inversions_closed G i))
  have hinc :
      (fst (complementVariety G i).toOver (inversionVariety G i).toOver ≫
        affineMorphism (rootQuotient G (simpleNoninversions G i)
          (simple_noninversions_closed G i))) *
      (snd (complementVariety G i).toOver (inversionVariety G i).toOver ≫
        affineMorphism (rootQuotient G (simpleInversions G i)
          (simple_inversions_closed G i))) = rootMultiplier G i := multiplication_congr
    (affineMorphism (rootQuotient G (simpleNoninversions G i)
      (simple_noninversions_closed G i)))
    (complementInclusion G i)
    (affineMorphism (rootQuotient G (simpleInversions G i)
      (simple_inversions_closed G i)))
    (inversionInclusion G i)
    (root_inclusion_affine G (simpleNoninversions G i)
      (simple_noninversions_closed G i)).symm
    (root_inclusion_affine G (simpleInversions G i)
      (simple_inversions_closed G i)).symm
  exact hraw.trans (hmul.symm.trans
    (congrArg (fun f => (productTensorIso G i).hom ≫ f) hinc))

private theorem opposite_product_ambient (i : G.rootBase.support) :
    (oppositeRootProductIso G i).hom ≫ oppositeUnipotentInclusion G =
      (productTensorIso G i).hom ≫
        (rootMultiplier G i ≫ (reductiveConjugation G G.longestPoint).hom) :=
  (oppositeRootProductIso_comp G i).trans
    ((congrArg (fun f => f ≫ (reductiveConjugation G G.longestPoint).hom)
      (positive_product_ambient G i)).trans (Category.assoc _ _ _))

private def simpleFactorIso (i : G.rootBase.support) :
    (complementVariety G i).toOver ⊗ (additiveVariety K).toOver ≅
      (complementVariety G i).toOver ⊗ (inversionVariety G i).toOver :=
  tensorIso (Iso.refl (complementVariety G i).toOver) (simpleRootIso G i)

/-- The simple-root additive parameter together with its complement gives coordinates
on the full opposite unipotent group. -/
def oppositeSimpleCoordinates (i : G.rootBase.support) :
    (rootSubsetVariety G
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))).toOver ⊗
      (additiveVariety K).toOver ≅ (oppositeUnipotentVariety G).toOver :=
  simpleFactorIso G i ≪≫ (productTensorIso G i).symm ≪≫ oppositeRootProductIso G i

/-- In simple-root coordinates the ambient group map is multiplication of the complement
and the chosen additive map, followed by longest-Weyl conjugation. -/
theorem oppositeSimpleCoordinates_comp (i : G.rootBase.support) :
    (oppositeSimpleCoordinates G i).hom ≫ oppositeUnipotentInclusion G =
      ((fst _ _ ≫ rootSubsetInclusion G
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i))) *
        (snd _ _ ≫ gaMorphism G (G.simpleRootMap i))) ≫
          (reductiveConjugation G G.longestPoint).hom := by
  have hchart := product_change_comp (simpleFactorIso G i) (productTensorIso G i)
    (oppositeRootProductIso G i) (oppositeUnipotentInclusion G)
    (rootMultiplier G i ≫ (reductiveConjugation G G.longestPoint).hom)
    (opposite_product_ambient G i)
  have hmul := tensor_mul_comp (𝟙 (complementVariety G i).toOver)
    (simpleRootIso G i).hom (complementInclusion G i) (inversionInclusion G i)
  have hfactor : (simpleFactorIso G i).hom ≫ rootMultiplier G i =
      (fst _ _ ≫ complementInclusion G i) *
        (snd _ _ ≫ gaMorphism G (G.simpleRootMap i)) := by
    exact hmul.trans (congrArg₂ (fun f g => f * g)
      (by simp only [Category.id_comp])
      (congrArg (fun f => snd _ _ ≫ f) (simpleRootIso_inclusion G i)))
  exact hchart.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ (reductiveConjugation G G.longestPoint).hom) hfactor))

end

end SchubertGeometry.DeterminantSection
