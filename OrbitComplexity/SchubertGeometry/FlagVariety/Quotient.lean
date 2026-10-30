import OrbitComplexity.SchubertGeometry.FlagVariety.QuotientCharts
import OrbitComplexity.SchubertGeometry.FlagVariety.Separated

/-! # The flag quotient morphism

The local unipotent projections glue to the quotient morphism from the reductive group.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem flagHom_ext (X : GroupActions.Variety K)
    (f g : X.scheme ⟶ flagScheme G)
    (hf : f ≫ flagSchemeToSpec G = X.toSpec)
    (hg : g ≫ flagSchemeToSpec G = X.toSpec)
    (H : ∀ p : X.points, p.val ≫ f = p.val ≫ g) : f = g := by
  have : LocallyOfFiniteType (f ≫ flagSchemeToSpec G) :=
    hf.symm ▸ X.locallyOfFiniteType
  refine AlgebraicGeometry.ext_of_apply_eq (flagSchemeToSpec G)
    Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ (hf.trans hg.symm)
  intro x _ hx
  obtain ⟨p, hp⟩ := X.pointsEquivClosedPoints.surjective ⟨x, hx⟩
  have hp' : X.pointMap p = x := congrArg Subtype.val hp
  have he := congrArg (fun k : Spec (CommRingCat.of K) ⟶ flagScheme G =>
    k (IsLocalRing.closedPoint K)) (H p)
  change f (X.pointMap p) = g (X.pointMap p) at he
  simpa only [hp'] using he

private theorem bigCellFlagChart_compatible (g h : G.points) :
    (bigCellOverlapFst G g h).left ≫ bigCellFlagChart G g =
      (bigCellOverlapSnd G g h).left ≫ bigCellFlagChart G h := by
  apply flagHom_ext G (bigCellOverlapVariety G g h)
  · rw [Category.assoc, bigCellFlagChart_toSpec]
    exact (bigCellOverlapFst G g h).w
  · rw [Category.assoc, bigCellFlagChart_toSpec]
    exact (bigCellOverlapSnd G g h).w
  · intro x
    have he := congrArg Subtype.val
      ((flagSchemeChartPoints_eq_iff G g h _ _).2 (bigCellOverlap_flags G g h x))
    calc
      x.val ≫ ((bigCellOverlapFst G g h).left ≫ bigCellFlagChart G g) =
          (GroupActions.Variety.mapPoints (bigCellOverlapFst G g h) x).val ≫
            bigCellFlagChart G g := (Category.assoc _ _ _).symm
      _ = _ := bigCellFlagChart_points G g _
      _ = _ := he
      _ = _ := (bigCellFlagChart_points G h _).symm
      _ = x.val ≫ ((bigCellOverlapSnd G g h).left ≫ bigCellFlagChart G h) :=
        Category.assoc _ _ _

/-- The quotient morphism to the flag scheme is glued from translated big cells. -/
def flagQuotient : (GroupActions.reductiveVariety G).scheme ⟶ flagScheme G :=
  (bigCellCover G).glueMorphisms (fun g => bigCellFlagChart G g) (fun g h =>
    bigCellFlagChart_compatible G g h)

/-- On a translated big cell the quotient morphism forgets the Borel coordinate. -/
theorem translatedBigCell_quotient (g : G.points) :
    (translatedBigCell G g).left ≫ flagQuotient G = bigCellFlagChart G g :=
  (bigCellCover G).ι_glueMorphisms _ _ g

/-- The quotient morphism is a morphism over the base field. -/
theorem flagQuotient_toSpec :
    flagQuotient G ≫ flagSchemeToSpec G = (GroupActions.reductiveVariety G).toSpec := by
  apply (bigCellCover G).hom_ext
  intro g
  change G.points at g
  change (translatedBigCell G g).left ≫ (flagQuotient G ≫ flagSchemeToSpec G) =
    (translatedBigCell G g).left ≫ (GroupActions.reductiveVariety G).toSpec
  rw [← Category.assoc, translatedBigCell_quotient, bigCellFlagChart_toSpec]
  exact (translatedBigCell G g).w.symm

/-- The quotient morphism sends a group point to its Borel coset. -/
theorem flagQuotient_points (g : G.points) :
    (GroupActions.reductivePointsEquiv G g).val ≫ flagQuotient G =
      (flagSchemePointsEquiv G (flagProjection G g)).val := by
  let x := (bigCellPointsEquiv G).symm (1, 1)
  have hx : GroupActions.Variety.mapPoints (translatedBigCell G g) x =
      GroupActions.reductivePointsEquiv G g := by
    rw [translatedBigCell_points]
    simp only [x, Equiv.apply_symm_apply, map_one, OneMemClass.coe_one, mul_one]
  have hq := congrArg (fun f => x.val ≫ f) (translatedBigCell_quotient G g)
  have hc : flagChartPoint G g 1 = flagProjection G g := by
    simp only [flagChartPoint, map_one, OneMemClass.coe_one, mul_one]
  calc
    (GroupActions.reductivePointsEquiv G g).val ≫ flagQuotient G =
        (GroupActions.Variety.mapPoints (translatedBigCell G g) x).val ≫
          flagQuotient G := congrArg (fun p => p.val ≫ flagQuotient G) hx.symm
    _ = x.val ≫ bigCellFlagChart G g := (Category.assoc _ _ _).trans hq
    _ = (flagSchemeChartPoints G g 1).val := by
      rw [bigCellFlagChart_points]
      simp only [x, Equiv.apply_symm_apply]
    _ = (flagSchemePointsEquiv G (flagProjection G g)).val := by
      exact congrArg Subtype.val ((flagSchemePointsEquiv_chart G g 1).symm.trans
        (congrArg (flagSchemePointsEquiv G) hc))

end
end SchubertGeometry