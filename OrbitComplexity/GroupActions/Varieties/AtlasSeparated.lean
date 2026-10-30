import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness from overlap graphs

The diagonal of a glued scheme restricts on each chart product to its overlap graph.
Closedness of all these graphs therefore gives separatedness over the base.

## Main definitions

* `gluedOverlapGraph`: the two overlap inclusions mapped to the product over the base.

## Main results

* `gluedOverlapGraph_fst`, `gluedOverlapGraph_snd`: the graph projections.
* `separated_of_glued_graphs`: closed overlap graphs give a separated structure morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GroupActions

universe u

variable (D : Scheme.GlueData.{u}) {S : Scheme.{u}} (s : D.glued ⟶ S)

/-- The two overlap projections determine a morphism into the product over the base. -/
noncomputable def gluedOverlapGraph (i j : D.J) :
    D.V (i, j) ⟶ pullback (D.ι i ≫ s) (D.ι j ≫ s) :=
  pullback.lift (D.f i j) (D.t i j ≫ D.f j i) (by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ s) (D.glue_condition i j).symm)

/-- The first projection of the overlap graph is the original overlap inclusion. -/
@[reassoc (attr := simp)]
theorem gluedOverlapGraph_fst (i j : D.J) :
    gluedOverlapGraph D s i j ≫ pullback.fst _ _ = D.f i j := by
  simp only [gluedOverlapGraph, pullback.lift_fst]

/-- The second projection of the overlap graph is the inclusion after transition. -/
@[reassoc (attr := simp)]
theorem gluedOverlapGraph_snd (i j : D.J) :
    gluedOverlapGraph D s i j ≫ pullback.snd _ _ = D.t i j ≫ D.f j i := by
  simp only [gluedOverlapGraph, pullback.lift_snd]

private theorem overlap_isPullback (i j : D.J) :
    IsPullback (D.f i j ≫ D.ι i) (gluedOverlapGraph D s i j) (pullback.diagonal s)
      (pullback.map (D.ι i ≫ s) (D.ι j ≫ s) s s
        (D.ι i) (D.ι j) (𝟙 S) (by simp) (by simp)) := by
  have hV : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
    IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
  refine (pullback_map_diagonal_isPullback (D.ι i) (D.ι j) s).of_iso'
    hV.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun f => f ≫ D.ι i) hV.isoPullback_hom_fst
  · apply pullback.hom_ext
    · simp [pullback.map, hV.isoPullback_hom_fst]
    · simp [pullback.map, hV.isoPullback_hom_snd]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- A glued scheme is separated over its base when all overlap graphs are closed immersions. -/
theorem separated_of_glued_graphs
    (H : ∀ i j, IsClosedImmersion (gluedOverlapGraph D s i j)) : IsSeparated s := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover
    (P := @IsClosedImmersion) (Scheme.Pullback.openCoverOfLeftRight D.openCover D.openCover s s)
  rintro ⟨i, j⟩
  change IsClosedImmersion (pullback.snd (pullback.diagonal s)
    (pullback.map (D.ι i ≫ s) (D.ι j ≫ s) s s
      (D.ι i) (D.ι j) (𝟙 S) (by simp) (by simp)))
  have hgraph := H i j
  let h := overlap_isPullback D s i j
  rw [← h.isoPullback_inv_snd]
  exact inferInstance

end GroupActions
