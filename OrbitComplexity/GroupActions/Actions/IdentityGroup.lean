import OrbitComplexity.GroupActions.Actions.Components
import OrbitComplexity.GroupActions.Actions.Subgroups
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections

/-! # The group structure on the identity component

Multiplication and inversion preserve the connected component of the unit. Restricting
these morphisms gives the identity component its group structure.

## Main results

* `GroupActions.identityComponentGroup`: the identity component is a group variety.
* `GroupActions.identityInclusion_isMonHom`: its inclusion respects multiplication and unit.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H : Variety K) [GrpObj H.toOver]

omit [IsAlgClosed K] in
private theorem unit_toUnit :
    toUnit (𝟙_ (Over (Spec (.of K)))) = 𝟙 _ := toUnit_unique _ _

private def liftIdentity {Z : Over (Spec (.of K))} (f : Z ⟶ H.toOver)
    (hf : Set.range (f.left : Z.left → H.scheme) ⊆ connectedComponent (H.pointMap 1)) :
    Z ⟶ (identityComponent H).toOver := by
  let i := identityInclusion H
  have hi : Set.range f.left ⊆ Set.range i.left := by
    rw [show i = identityInclusion H from rfl, identityInclusion_range]
    exact hf
  refine Over.homMk (IsOpenImmersion.lift i.left f.left hi) ?_
  change IsOpenImmersion.lift i.left f.left hi ≫ (identityComponent H).toSpec = Z.hom
  rw [← show i.left ≫ H.toSpec = (identityComponent H).toSpec from i.w,
    ← Category.assoc, IsOpenImmersion.lift_fac]
  exact f.w

omit [IsAlgClosed K] in
private theorem liftIdentity_fac {Z : Over (Spec (.of K))} (f : Z ⟶ H.toOver)
    (hf : Set.range (f.left : Z.left → H.scheme) ⊆ connectedComponent (H.pointMap 1)) :
    liftIdentity H f hf ≫ identityInclusion H = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

omit [IsAlgClosed K] in
private theorem connected_range {Z : Over (Spec (.of K))} [ConnectedSpace Z.left]
    (f : Z ⟶ H.toOver) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z)
    (hz : z ≫ f = η[H.toOver]) :
    Set.range (f.left : Z.left → H.scheme) ⊆ connectedComponent (H.pointMap 1) := by
  apply (isPreconnected_range f.left.continuous).subset_connectedComponent
  refine ⟨z.left (IsLocalRing.closedPoint K), ?_⟩
  have he := congrArg (fun g ↦ g.left (IsLocalRing.closedPoint K)) hz
  change f.left (z.left (IsLocalRing.closedPoint K)) =
    η[H.toOver].left (IsLocalRing.closedPoint K) at he
  rw [unitPoint_left] at he
  exact he

private def identityUnit : 𝟙_ (Over (Spec (.of K))) ⟶ (identityComponent H).toOver :=
  liftIdentity H η[H.toOver] (by
    have : Subsingleton (𝟙_ (Over (Spec (.of K)))).left :=
      inferInstanceAs (Subsingleton (Spec (.of K)))
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz, unitPoint_left]
    exact mem_connectedComponent)

omit [IsAlgClosed K] in
private theorem identityUnit_fac : identityUnit H ≫ identityInclusion H = η[H.toOver] :=
  liftIdentity_fac H _ _

private def identityMul : (identityComponent H).toOver ⊗ (identityComponent H).toOver ⟶
    (identityComponent H).toOver :=
  let C := identityComponent H
  let i := identityInclusion H
  let P := Variety.productVariety C C
  letI : IsIntegral P.scheme := Variety.product_integral C C
  liftIdentity H ((i ⊗ₘ i) ≫ μ[H.toOver])
    (connected_range H _ (lift (identityUnit H) (identityUnit H)) (by
      dsimp only [i]
      simp only [lift_map_assoc, identityUnit_fac]
      simpa only [Category.id_comp] using
        MonObj.lift_comp_one_left (𝟙 _) η[H.toOver]))

private theorem identityMul_fac : identityMul H ≫ identityInclusion H =
    (identityInclusion H ⊗ₘ identityInclusion H) ≫ μ[H.toOver] := by
  dsimp only [identityMul]
  exact liftIdentity_fac H _ _

private def identityInv : (identityComponent H).toOver ⟶ (identityComponent H).toOver :=
  letI : ConnectedSpace (identityComponent H).toOver.left :=
    inferInstanceAs (ConnectedSpace (identityComponent H).scheme)
  liftIdentity H (identityInclusion H ≫ ι[H.toOver])
    (connected_range H _ (identityUnit H) (by
      rw [← Category.assoc, identityUnit_fac]
      have hi : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ H.toOver)⁻¹ = 1 := inv_one
      change (toUnit _ ≫ η[H.toOver]) ≫ ι[H.toOver] = toUnit _ ≫ η[H.toOver] at hi
      simpa only [unit_toUnit, Category.id_comp] using hi))

omit [IsAlgClosed K] in
private theorem identityInv_fac : identityInv H ≫ identityInclusion H =
    identityInclusion H ≫ ι[H.toOver] := liftIdentity_fac H _ _

/-- The identity component has the group law restricted from the ambient group. -/
instance identityComponentGroup : GrpObj (identityComponent H).toOver :=
  grpObjOfMono (identityInclusion H) (identityUnit H) (identityMul H) (identityInv H)
    (identityUnit_fac H) (identityMul_fac H) (identityInv_fac H)

/-- The inclusion of the identity component preserves the group operations. -/
instance identityInclusion_isMonHom : IsMonHom (identityInclusion H) where
  one_hom := identityUnit_fac H
  mul_hom := identityMul_fac H

end

end GroupActions
