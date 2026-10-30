import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import OrbitComplexity.GroupActions.Varieties.ReductiveConjugation
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.SchubertGeometry.FlagVariety.ChartMorphisms

/-! # Inversion-root subgroups in opposite charts

Weyl conjugation embeds an inversion-root subgroup as a closed subvariety of the opposite
unipotent subgroup. The corresponding flag chart realizes its Schubert-cell morphism.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- Points of the inversion-root variety form the inversion-root point subgroup. -/
def schubertUnipotentPointsEquiv (w : G.weylGroup) :
    (schubertUnipotent G w).points ≃* schubertUnipotentPoints G w :=
  GroupActions.rootSubsetPointsMulEquiv G _
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)

/-- Conjugate the inversion-root subgroup by the inverse Weyl representative. -/
def schubertConjugateMorphism (w : G.weylGroup) :
    (schubertUnipotent G w).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  schubertUnipotentInclusion G w ≫
    (GroupActions.reductiveConjugation G (G.weylPoint w)⁻¹).hom

/-- The conjugated inversion-root morphism is a closed immersion. -/
instance schubertConjugate_isClosed (w : G.weylGroup) :
    IsClosedImmersion (schubertConjugateMorphism G w).left := by
  change IsClosedImmersion ((schubertUnipotentInclusion G w).left ≫
    (GroupActions.reductiveConjugation G (G.weylPoint w)⁻¹).hom.left)
  infer_instance

/-- The conjugated root morphism acts by ordinary Weyl conjugation on points. -/
theorem schubertConjugateMorphism_points (w : G.weylGroup)
    (x : (schubertUnipotent G w).points) :
    GroupActions.Variety.mapPoints (schubertConjugateMorphism G w) x =
      GroupActions.reductivePointsEquiv G ((G.weylPoint w)⁻¹ *
        (schubertUnipotentPointsEquiv G w x : G.points) * G.weylPoint w) := by
  have hi : GroupActions.Variety.mapPoints (schubertUnipotentInclusion G w) x =
      GroupActions.reductivePointsEquiv G (schubertUnipotentPointsEquiv G w x) :=
    GroupActions.rootSubsetInclusion_points G _ _ x
  have hc : GroupActions.Variety.mapPoints
      (GroupActions.reductiveConjugation G (G.weylPoint w)⁻¹).hom
      (GroupActions.reductivePointsEquiv G (schubertUnipotentPointsEquiv G w x)) =
      GroupActions.reductivePointsEquiv G ((G.weylPoint w)⁻¹ *
        (schubertUnipotentPointsEquiv G w x : G.points) * G.weylPoint w) := by
    simpa only [inv_inv] using
      (GroupActions.reductiveConjugation_points G (G.weylPoint w)⁻¹
        (schubertUnipotentPointsEquiv G w x))
  exact (GroupActions.Variety.mapPoints_comp (schubertUnipotentInclusion G w)
    (GroupActions.reductiveConjugation G (G.weylPoint w)⁻¹).hom x).trans
    ((congrArg (GroupActions.Variety.mapPoints
      (GroupActions.reductiveConjugation G (G.weylPoint w)⁻¹).hom) hi).trans hc)

private instance schubertRootReduced (w : G.weylGroup) :
    IsReduced (schubertUnipotent G w).toOver.left := by
  change IsReduced (schubertUnipotent G w).scheme
  exact (schubertUnipotent G w).reduced

private theorem schubertConjugate_range (w : G.weylGroup) :
    Set.range ((schubertConjugateMorphism G w).left :
      (schubertUnipotent G w).scheme → (GroupActions.reductiveVariety G).scheme) ⊆
      Set.range ((GroupActions.oppositeUnipotentInclusion G).left :
        (GroupActions.oppositeUnipotentVariety G).scheme →
          (GroupActions.reductiveVariety G).scheme) := by
  apply GroupActions.Variety.range_subset_of_mapPoints
  rintro p ⟨x, rfl⟩
  let g := (G.weylPoint w)⁻¹ * (schubertUnipotentPointsEquiv G w x : G.points) * G.weylPoint w
  have hg : g ∈ G.oppositeUnipotentPoints :=
    G.inversionPoints_conj_opposite w _ (schubertUnipotentPointsEquiv G w x).property
  refine ⟨(GroupActions.oppositeUnipotentPointsMulEquiv G).symm ⟨g, hg⟩, ?_⟩
  rw [GroupActions.oppositeUnipotentInclusion_points, MulEquiv.apply_symm_apply]
  exact (schubertConjugateMorphism_points G w x).symm

/-- The inversion-root subgroup maps into the opposite unipotent subgroup by Weyl conjugation. -/
def schubertOppositeMorphism (w : G.weylGroup) :
    (schubertUnipotent G w).toOver ⟶ (GroupActions.oppositeUnipotentVariety G).toOver := by
  let f : (schubertUnipotent G w).scheme ⟶ (GroupActions.reductiveVariety G).scheme :=
    (schubertConjugateMorphism G w).left
  let i : (GroupActions.oppositeUnipotentVariety G).scheme ⟶
      (GroupActions.reductiveVariety G).scheme := (GroupActions.oppositeUnipotentInclusion G).left
  let g := GroupActions.liftPreimmersion i f (schubertConjugate_range G w)
  refine Over.homMk g ?_
  change g ≫ (GroupActions.oppositeUnipotentVariety G).toSpec = (schubertUnipotent G w).toSpec
  rw [← (show i ≫ (GroupActions.reductiveVariety G).toSpec =
    (GroupActions.oppositeUnipotentVariety G).toSpec from
      (GroupActions.oppositeUnipotentInclusion G).w), ← Category.assoc]
  dsimp only [g]
  rw [GroupActions.liftPreimmersion_fac]
  exact (schubertConjugateMorphism G w).w

/-- The opposite-subgroup factorization recovers the conjugated ambient root morphism. -/
theorem schubertOppositeMorphism_fac (w : G.weylGroup) :
    schubertOppositeMorphism G w ≫ GroupActions.oppositeUnipotentInclusion G =
      schubertConjugateMorphism G w := by
  apply Over.OverMorphism.ext
  exact GroupActions.liftPreimmersion_fac _ _ (schubertConjugate_range G w)

/-- The conjugated inversion-root subgroup is closed in the opposite unipotent subgroup. -/
instance schubertOpposite_isClosed (w : G.weylGroup) :
    IsClosedImmersion (schubertOppositeMorphism G w).left := by
  have : IsClosedImmersion ((schubertOppositeMorphism G w).left ≫
      (GroupActions.oppositeUnipotentInclusion G).left) := by
    change IsClosedImmersion
      (schubertOppositeMorphism G w ≫ GroupActions.oppositeUnipotentInclusion G).left
    rw [schubertOppositeMorphism_fac]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (schubertOppositeMorphism G w).left
    (GroupActions.oppositeUnipotentInclusion G).left

/-- Rational points of the opposite-subgroup morphism are Weyl-conjugated root points. -/
theorem schubertOppositeMorphism_points (w : G.weylGroup)
    (x : (schubertUnipotent G w).points) :
    (GroupActions.oppositeUnipotentPointsMulEquiv G
      (GroupActions.Variety.mapPoints (schubertOppositeMorphism G w) x) : G.points) =
        (G.weylPoint w)⁻¹ * (schubertUnipotentPointsEquiv G w x : G.points) * G.weylPoint w := by
  apply (GroupActions.reductivePointsEquiv G).injective
  rw [← GroupActions.oppositeUnipotentInclusion_points,
    ← GroupActions.Variety.mapPoints_comp, schubertOppositeMorphism_fac,
    schubertConjugateMorphism_points]

end
end SchubertGeometry
