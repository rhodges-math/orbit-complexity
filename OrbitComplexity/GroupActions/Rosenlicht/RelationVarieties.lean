import OrbitComplexity.GroupActions.Rosenlicht.ProductSections
import OrbitComplexity.GroupActions.Varieties.Subvarieties
import OrbitComplexity.GroupActions.Varieties.Factorization
import OrbitComplexity.GroupActions.Varieties.Images

/-!
# Varieties of orbit relations

The map sending a group element and a point to the point and its translate
has a reduced image closure. Its projection to the original variety is
surjective, and the relation map dominates this closure.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The orbit relation morphism sends a group element and a point to that point
and its translate. -/
def orbitRelationMorphism :
    (productVariety H X).toOver ⟶ (productVariety X X).toOver :=
  lift (snd H.toOver X.toOver) (ModObj.smul (M := H.toOver) (X := X.toOver))

/-- The reduced closed variety underlying the closure of the orbit relation. -/
def orbitRelationVariety : GroupActions.Variety K :=
  (productVariety X X).closedSubvariety
    ⟨closure (Set.range (orbitRelationMorphism H X).left), isClosed_closure⟩

/-- The inclusion of the orbit relation closure into the product. -/
def orbitRelationInclusion :
    (orbitRelationVariety H X).toOver ⟶ (productVariety X X).toOver :=
  (productVariety X X).closedInclusion
    ⟨closure (Set.range (orbitRelationMorphism H X).left), isClosed_closure⟩

/-- The orbit relation closure has the prescribed closed image. -/
theorem orbitRelationInclusion_range :
    Set.range (orbitRelationInclusion H X).left =
      closure (Set.range (orbitRelationMorphism H X).left) :=
  (productVariety X X).closedInclusion_range _

/-- The inclusion of the orbit relation closure is a closed immersion. -/
instance orbitRelationInclusion_closed : IsClosedImmersion (orbitRelationInclusion H X).left :=
  inferInstanceAs (IsClosedImmersion ((productVariety X X).closedInclusion _).left)

private lemma relation_range_subset :
    Set.range (orbitRelationMorphism H X).left ⊆
      Set.range (orbitRelationInclusion H X).left := by
  rw [orbitRelationInclusion_range]
  exact subset_closure

private instance productOver_reduced : IsReduced (productVariety H X).toOver.left :=
  (productVariety H X).reduced

/-- The orbit relation morphism factors through its reduced image closure. -/
def orbitRelationFactor :
    (productVariety H X).toOver ⟶ (orbitRelationVariety H X).toOver := by
  let g := liftPreimmersion (orbitRelationInclusion H X).left
    (orbitRelationMorphism H X).left (relation_range_subset H X)
  refine Over.homMk g ?_
  change g ≫ ((orbitRelationInclusion H X).left ≫ (productVariety X X).toSpec) =
    (productVariety H X).toSpec
  dsimp only [g]
  rw [← Category.assoc, liftPreimmersion_fac]
  exact (orbitRelationMorphism H X).w

/-- The factorization recovers the orbit relation after inclusion. -/
theorem orbitRelationFactor_fac :
    orbitRelationFactor H X ≫ orbitRelationInclusion H X = orbitRelationMorphism H X := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (orbitRelationInclusion H X).left
    (orbitRelationMorphism H X).left (relation_range_subset H X)

private def relationHomeomorph :
    (orbitRelationVariety H X).scheme ≃ₜ
      closure (Set.range (orbitRelationMorphism H X).left) :=
  (orbitRelationInclusion H X).left.isEmbedding.toHomeomorph.trans
    (.setCongr (orbitRelationInclusion_range H X))

/-- The closure of the orbit relation of an irreducible group is irreducible. -/
instance orbitRelationVariety_irreducible :
    IrreducibleSpace (orbitRelationVariety H X).scheme := by
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  have hr : IsIrreducible (Set.range (orbitRelationMorphism H X).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (productVariety H X).scheme).image
        (orbitRelationMorphism H X).left (orbitRelationMorphism H X).left.continuous.continuousOn
  have : IrreducibleSpace (closure (Set.range (orbitRelationMorphism H X).left)) :=
    isIrreducible_iff_irreducibleSpace.mp hr.closure
  exact (relationHomeomorph H X).irreducibleSpace_iff.mpr inferInstance

/-- The orbit relation is dense in its reduced image closure. -/
instance orbitRelationFactor_dominant : IsDominant (orbitRelationFactor H X).left := by
  constructor
  apply denseRange_iff_closure_range.mpr
  rw [(orbitRelationInclusion H X).left.isEmbedding.closure_eq_preimage_closure_image]
  have hr : (orbitRelationInclusion H X).left '' Set.range (orbitRelationFactor H X).left =
      Set.range (orbitRelationMorphism H X).left := by
    rw [← Set.range_comp]
    congr 1
    funext x
    exact congrArg (fun f ↦ f.left x) (orbitRelationFactor_fac H X)
  rw [hr, ← orbitRelationInclusion_range H X]
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨x, rfl⟩

/-- The first projection from the orbit relation closure to the original variety. -/
def orbitRelationProjection : (orbitRelationVariety H X).toOver ⟶ X.toOver :=
  orbitRelationInclusion H X ≫ fst X.toOver X.toOver

/-- The projection of the orbit relation is its point coordinate. -/
theorem orbitRelationProjection_fac :
    orbitRelationFactor H X ≫ orbitRelationProjection H X = snd H.toOver X.toOver := by
  rw [orbitRelationProjection, ← Category.assoc, orbitRelationFactor_fac,
    orbitRelationMorphism, lift_fst]

/-- The orbit relation projection is surjective, using the identity group section. -/
instance orbitRelationProjection_surjective : Surjective (orbitRelationProjection H X).left := by
  have hs : (pointSection H X 1 ≫ orbitRelationFactor H X) ≫
      orbitRelationProjection H X = 𝟙 X.toOver := by
    rw [Category.assoc, orbitRelationProjection_fac, pointSection_snd]
  constructor
  intro x
  refine ⟨(pointSection H X 1 ≫ orbitRelationFactor H X).left x, ?_⟩
  exact congrArg (fun f ↦ f.left x) hs

end

end GroupActions.Variety
