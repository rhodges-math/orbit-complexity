import OrbitComplexity.GroupActions.Rosenlicht.AffineRelations
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-!
# RelationChartLifts
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A relation point lifts to the relation chart whenever its two coordinates
lift to the chosen open charts. -/
theorem relationChartPoint_of_pair (U V : X.scheme.Opens)
    (p : (X.openSubvariety U).points) (q : (X.openSubvariety V).points)
    (r : Spec (.of K) ⟶ (orbitRelationVariety H X).scheme)
    (hfirst : r ≫ (orbitRelationProjection H X).left = p.val ≫ U.ι)
    (hsecond : r ≫ (orbitRelationSecond H X).left = q.val ≫ V.ι) :
    ∃ t : Spec (.of K) ⟶ relationChart H X U V,
      t ≫ relationChartFirst H X U V = p.val ∧
      t ≫ relationChartSecond H X U V = q.val := by
  let p' : Spec (.of K) ⟶ U.toScheme := p.val
  let q' : Spec (.of K) ⟶ V.toScheme := q.val
  have hp : p' ≫ (U.ι ≫ X.toSpec) = 𝟙 _ := p.property
  have hq : q' ≫ (V.ι ≫ X.toSpec) = 𝟙 _ := q.property
  have hpq : p' ≫ (U.ι ≫ X.toSpec) = q' ≫ (V.ι ≫ X.toSpec) := hp.trans hq.symm
  let a : Spec (.of K) ⟶ pullback (U.ι ≫ X.toSpec) (V.ι ≫ X.toSpec) :=
    pullback.lift p' q' hpq
  have hc : r ≫ (orbitRelationInclusion H X).left =
      a ≫ productOpenMap X.toSpec X.toSpec U V := by
    apply pullback.hom_ext
    · change r ≫ (orbitRelationProjection H X).left =
        (a ≫ productOpenMap X.toSpec X.toSpec U V) ≫ pullback.fst X.toSpec X.toSpec
      rw [Category.assoc, productOpenMap_fst, ← Category.assoc]
      dsimp only [a]
      rw [pullback.lift_fst]
      exact hfirst
    · change r ≫ (orbitRelationSecond H X).left =
        (a ≫ productOpenMap X.toSpec X.toSpec U V) ≫ pullback.snd X.toSpec X.toSpec
      rw [Category.assoc, productOpenMap_snd, ← Category.assoc]
      dsimp only [a]
      rw [pullback.lift_snd]
      exact hsecond
  let t : Spec (.of K) ⟶ relationChart H X U V := pullback.lift r a hc
  have ht : t ≫ relationChartProduct H X U V = a := pullback.lift_snd r a hc
  refine ⟨t, ?_, ?_⟩
  · change t ≫ (relationChartProduct H X U V ≫ pullback.fst _ _) = p.val
    rw [← Category.assoc, ht]
    exact pullback.lift_fst p' q' _
  · change t ≫ (relationChartProduct H X U V ≫ pullback.snd _ _) = q.val
    rw [← Category.assoc, ht]
    exact pullback.lift_snd p' q' _

end

end GroupActions.Variety
