import OrbitComplexity.SchubertGeometry.FlagVariety.ChartMorphisms
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

/-! # Local Borel torsor charts of the flag quotient

The translated big cell is the inverse image of its open flag chart. Its product
coordinates therefore trivialize the flag quotient, with right multiplication on the
Borel coordinate agreeing with right multiplication in the reductive group.

## Main definitions

* `SchubertGeometry.flagTorsorIso`: the product chart of the pulled-back quotient.

## Main results

* `SchubertGeometry.flagTorsorPullback`: the translated big-cell square is cartesian.
* `SchubertGeometry.flagTorsorIso_mul`: the chart respects right Borel multiplication.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem quotient_chart (g : G.points) :
    translatedBigCell G g ≫ flagQuotientMorphism G =
      bigCellFst G ≫ flagChartMorphism G g := by
  apply Over.OverMorphism.ext
  exact translatedBigCell_quotient G g

/-- A translated unipotent section represents its corresponding open flag chart. -/
theorem flagChartMap_quotient (g : G.points) :
    flagChartMap G g ≫ flagQuotientMorphism G = flagChartMorphism G g := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  rw [GroupActions.Variety.mapPoints_comp, flagChartMap_points,
    flagQuotientMorphism_points, flagChartMorphism_points]
  rfl

private theorem point_image (g : G.points)
    (x : (GroupActions.reductiveVariety G).points) :
    GroupActions.Variety.mapPoints (flagQuotientMorphism G) x ∈
        Set.range (GroupActions.Variety.mapPoints (flagChartMorphism G g)) ↔
      x ∈ Set.range (GroupActions.Variety.mapPoints (translatedBigCell G g)) := by
  obtain ⟨a, rfl⟩ := (GroupActions.reductivePointsEquiv G).surjective x
  constructor
  · rintro ⟨v, hv⟩
    rw [flagChartMorphism_points, flagQuotientMorphism_points] at hv
    have hc := (flagVarietyPointsEquiv G).injective hv
    have hb := (flagProjection_eq_iff G _ _).mp hc
    let b : G.borelPoints :=
      ⟨(g * (GroupActions.oppositeUnipotentPointsMulEquiv G v : G.points))⁻¹ * a, hb⟩
    refine ⟨(bigCellPointsEquiv G).symm
      (v, (GroupActions.borelPointsMulEquiv G).symm b), ?_⟩
    rw [translatedBigCell_points, Equiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    apply congrArg (GroupActions.reductivePointsEquiv G)
    dsimp only [b]
    group
  · rintro ⟨p, hp⟩
    refine ⟨GroupActions.Variety.mapPoints (bigCellFst G) p, ?_⟩
    have h := congrArg (fun f => GroupActions.Variety.mapPoints f p) (quotient_chart G g)
    simpa only [GroupActions.Variety.mapPoints_comp, hp] using h.symm

omit [CharZero K] in
private theorem open_le_of_points (X : GroupActions.Variety K) (U V : X.scheme.Opens)
    (h : ∀ x : X.points, X.pointMap x ∈ U → X.pointMap x ∈ V) : U ≤ V := by
  have hi := GroupActions.Variety.range_subset_open_of_points (X.openInclusion U) V
    (fun x => h _ (((X.openSubvariety U).pointMap x).property))
  rwa [X.openInclusion_range] at hi

private theorem preimage_chart (g : G.points) :
    (flagQuotientMorphism G).left ⁻¹ᵁ (flagChartMorphism G g).left.opensRange =
      (translatedBigCell G g).left.opensRange := by
  apply le_antisymm
  · apply open_le_of_points
    intro x hx
    have hx' : GroupActions.Variety.mapPoints (flagQuotientMorphism G) x ∈
        Set.range (GroupActions.Variety.mapPoints (flagChartMorphism G g)) := by
      rw [GroupActions.Variety.range_mapPoints]
      exact hx
    obtain ⟨p, hp⟩ := (point_image G g x).mp hx'
    exact ⟨(bigCellVariety G).pointMap p,
      congrArg (GroupActions.reductiveVariety G).pointMap hp⟩
  · apply open_le_of_points
    intro x hx
    have hx' : x ∈ Set.range
        (GroupActions.Variety.mapPoints (translatedBigCell G g)) := by
      rw [GroupActions.Variety.range_mapPoints]
      exact hx
    obtain ⟨p, hp⟩ := (point_image G g x).mpr hx'
    exact ⟨(GroupActions.oppositeUnipotentVariety G).pointMap p,
      congrArg (flagVariety G).pointMap hp⟩

/-- The translated big cell is the pullback of its open flag chart. -/
theorem flagTorsorPullback (g : G.points) :
    IsPullback (bigCellFst G) (translatedBigCell G g)
      (flagChartMorphism G g) (flagQuotientMorphism G) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of K)))
  exact IsOpenImmersion.isPullback (bigCellFst G).left (translatedBigCell G g).left
    (flagChartMorphism G g).left (flagQuotientMorphism G).left
    (congrArg Over.Hom.left (quotient_chart G g)) (preimage_chart G g)

private theorem unipotentReduced : IsReduced G.oppositeUnipotentAlgebra :=
  (affine_isReduced_iff _).mp (GroupActions.oppositeUnipotentVariety G).reduced

omit [CharZero K] in
private theorem borelReduced : IsReduced G.borelAlgebra :=
  (affine_isReduced_iff _).mp (GroupActions.borelVariety G).reduced

private theorem productReduced :
    IsReduced (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra) :=
  (affine_isReduced_iff _).mp (bigCellVariety G).reduced

attribute [local instance] unipotentReduced borelReduced productReduced

private theorem productFiniteType :
    Algebra.FiniteType K (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra) := by
  let : Algebra.Smooth K G.oppositeUnipotentAlgebra := G.oppositeUnipotent_smooth
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  let : Algebra.Smooth K (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra) :=
    Algebra.Smooth.comp K G.oppositeUnipotentAlgebra _
  infer_instance

attribute [local instance] productFiniteType

private def tensorIso : (bigCellVariety G).toOver ≅
    (GroupActions.oppositeUnipotentVariety G).toOver ⊗
      (GroupActions.borelVariety G).toOver :=
  GroupActions.affineTensorIso K G.oppositeUnipotentAlgebra G.borelAlgebra

private theorem tensorIso_fst : (tensorIso G).hom ≫
    fst (GroupActions.oppositeUnipotentVariety G).toOver
      (GroupActions.borelVariety G).toOver = bigCellFst G :=
  GroupActions.affineTensorIso_fst K G.oppositeUnipotentAlgebra G.borelAlgebra

private theorem tensorIso_snd : (tensorIso G).hom ≫
    snd (GroupActions.oppositeUnipotentVariety G).toOver
      (GroupActions.borelVariety G).toOver = bigCellSnd G :=
  GroupActions.affineTensorIso_snd K G.oppositeUnipotentAlgebra G.borelAlgebra

/-- The flag quotient becomes the product with the Borel over each unipotent chart. -/
def flagTorsorIso (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).toOver ⊗
        (GroupActions.borelVariety G).toOver ≅
      pullback (flagChartMorphism G g) (flagQuotientMorphism G) :=
  (tensorIso G).symm ≪≫
    (flagTorsorPullback G g).isoPullback

/-- A local torsor trivialization preserves the unipotent base coordinate. -/
theorem flagTorsorIso_fst (g : G.points) :
    (flagTorsorIso G g).hom ≫
        pullback.fst (flagChartMorphism G g) (flagQuotientMorphism G) =
      fst (GroupActions.oppositeUnipotentVariety G).toOver
        (GroupActions.borelVariety G).toOver := by
  dsimp only [flagTorsorIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]
  apply (cancel_epi
    (tensorIso G).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (tensorIso_fst G).symm

private theorem flagTorsorIso_snd (g : G.points) :
    (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G) =
      (tensorIso G).inv ≫
        translatedBigCell G g := by
  dsimp only [flagTorsorIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : GroupActions.Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    GroupActions.Variety.mapPoints (f * g) x =
      GroupActions.Variety.mapPoints f x * GroupActions.Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [GroupActions.Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

private theorem translatedBigCell_mul (g : G.points) :
    translatedBigCell G g =
      (bigCellFst G ≫ flagChartMap G g) * (bigCellSnd G ≫ GroupActions.borelInclusion G) := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  rw [mapPoints_mul, GroupActions.Variety.mapPoints_comp,
    GroupActions.Variety.mapPoints_comp, flagChartMap_points,
    GroupActions.borelInclusion_points, translatedBigCell_points]
  change (GroupActions.reductivePointsMulEquiv G) _ =
    (GroupActions.reductivePointsMulEquiv G) _ * (GroupActions.reductivePointsMulEquiv G) _
  rw [← (GroupActions.reductivePointsMulEquiv G).map_mul]
  rw [← bigCellPointsEquiv_fst, ← bigCellPointsEquiv_snd]
  exact congrArg (GroupActions.reductivePointsEquiv G) (mul_assoc _ _ _).symm

/-- The group projection of the chart multiplies its section by its Borel coordinate. -/
theorem flagTorsorIso_group (g : G.points) :
    (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G) =
      (fst (GroupActions.oppositeUnipotentVariety G).toOver
        (GroupActions.borelVariety G).toOver ≫ flagChartMap G g) *
      (snd (GroupActions.oppositeUnipotentVariety G).toOver
        (GroupActions.borelVariety G).toOver ≫ GroupActions.borelInclusion G) := by
  rw [flagTorsorIso_snd, translatedBigCell_mul, MonObj.comp_mul]
  congr 1
  · rw [← Category.assoc]
    congr 1
    apply (cancel_epi
      (tensorIso G).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (tensorIso_fst G).symm
  · rw [← Category.assoc]
    congr 1
    apply (cancel_epi
      (tensorIso G).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (tensorIso_snd G).symm

/-- Local torsor charts commute with right multiplication by the Borel group. -/
theorem flagTorsorIso_mul (g : G.points) (Z : Over (Spec (CommRingCat.of K)))
    (v : Z ⟶ (GroupActions.oppositeUnipotentVariety G).toOver)
    (b c : Z ⟶ (GroupActions.borelVariety G).toOver) :
    lift v (b * c) ≫ (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G) =
      (lift v b ≫ (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G)) *
        (c ≫ GroupActions.borelInclusion G) := by
  simp only [flagTorsorIso_group, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    MonObj.mul_comp, mul_assoc]

end
end SchubertGeometry
