import OrbitComplexity.GroupActions.Rosenlicht.RelationProjections
import OrbitComplexity.GroupActions.Rosenlicht.ProductOpenCharts
import OrbitComplexity.GroupActions.Rosenlicht.AffineProductCoordinates

/-!
# Affine charts of orbit relations
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]
variable (U V : X.scheme.Opens)

private def relationProductMap : (orbitRelationVariety H X).scheme ⟶
    pullback X.toSpec X.toSpec := (orbitRelationInclusion H X).left

/-- The part of the orbit relation closure whose two coordinates lie in
specified open charts. -/
def relationChart : Scheme :=
  pullback (relationProductMap H X) (productOpenMap X.toSpec X.toSpec U V)

/-- The open inclusion of a chart of the orbit relation closure. -/
def relationChartInclusion : relationChart H X U V ⟶ (orbitRelationVariety H X).scheme :=
  pullback.fst _ _

/-- The closed immersion of the relation chart into the product of its two charts. -/
def relationChartProduct : relationChart H X U V ⟶
    pullback (U.ι ≫ X.toSpec) (V.ι ≫ X.toSpec) := pullback.snd _ _

/-- The inclusion of a relation chart is an open immersion. -/
instance relationChartInclusion_open : IsOpenImmersion (relationChartInclusion H X U V) := by
  dsimp only [relationChartInclusion, relationChart]
  infer_instance

/-- A relation chart is closed in its affine product chart. -/
instance relationChartProduct_closed : IsClosedImmersion (relationChartProduct H X U V) := by
  have : IsClosedImmersion (relationProductMap H X) := orbitRelationInclusion_closed H X
  dsimp only [relationChartProduct, relationChart]
  infer_instance

/-- A relation chart meets every pair of nonempty open coordinate charts. -/
theorem relationChart_nonempty (hU : (U : Set X.scheme).Nonempty)
    (hV : (V : Set X.scheme).Nonempty) : Nonempty (relationChart H X U V) := by
  have : IsDominant (relationProductMap H X ≫ pullback.fst X.toSpec X.toSpec) :=
    inferInstanceAs (IsDominant (orbitRelationProjection H X).left)
  have : IsDominant (relationProductMap H X ≫ pullback.snd X.toSpec X.toSpec) :=
    inferInstanceAs (IsDominant (orbitRelationSecond H X).left)
  exact productChart_pullback_nonempty X.toSpec X.toSpec U V (relationProductMap H X) hU hV

/-- A nonempty chart of the orbit relation closure is integral. -/
theorem relationChart_isIntegral (hU : (U : Set X.scheme).Nonempty)
    (hV : (V : Set X.scheme).Nonempty) : IsIntegral (relationChart H X U V) := by
  have := relationChart_nonempty H X U V hU hV
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  exact isIntegral_of_isOpenImmersion (relationChartInclusion H X U V)

/-- The relation chart over two affine coordinate charts is affine. -/
theorem relationChart_isAffine (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffine (relationChart H X U V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  exact isAffine_of_isAffineHom (relationChartProduct H X U V)

/-- The first projection of a relation chart to its coordinate chart. -/
def relationChartFirst : relationChart H X U V ⟶ U.toScheme :=
  relationChartProduct H X U V ≫ pullback.fst _ _

/-- The second projection of a relation chart to its coordinate chart. -/
def relationChartSecond : relationChart H X U V ⟶ V.toScheme :=
  relationChartProduct H X U V ≫ pullback.snd _ _

/-- Including the first chart projection recovers the ambient relation projection. -/
theorem relationChartFirst_fac :
    relationChartFirst H X U V ≫ U.ι =
      relationChartInclusion H X U V ≫ (orbitRelationProjection H X).left := by
  dsimp only [relationChartFirst]
  rw [Category.assoc, ← productOpenMap_fst]
  change relationChartProduct H X U V ≫
    (productOpenMap X.toSpec X.toSpec U V ≫ pullback.fst X.toSpec X.toSpec) =
    relationChartInclusion H X U V ≫
      (relationProductMap H X ≫ pullback.fst X.toSpec X.toSpec)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ pullback.fst X.toSpec X.toSpec)
    (pullback.condition (f := relationProductMap H X)
      (g := productOpenMap X.toSpec X.toSpec U V)).symm

/-- Including the second chart projection recovers the ambient relation projection. -/
theorem relationChartSecond_fac :
    relationChartSecond H X U V ≫ V.ι =
      relationChartInclusion H X U V ≫ (orbitRelationSecond H X).left := by
  dsimp only [relationChartSecond]
  rw [Category.assoc, ← productOpenMap_snd]
  change relationChartProduct H X U V ≫
    (productOpenMap X.toSpec X.toSpec U V ≫ pullback.snd X.toSpec X.toSpec) =
    relationChartInclusion H X U V ≫
      (relationProductMap H X ≫ pullback.snd X.toSpec X.toSpec)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ pullback.snd X.toSpec X.toSpec)
    (pullback.condition (f := relationProductMap H X)
      (g := productOpenMap X.toSpec X.toSpec U V)).symm

/-- A nonempty relation chart is dense in the relation closure. -/
theorem relationChartInclusion_dominant (hU : (U : Set X.scheme).Nonempty)
    (hV : (V : Set X.scheme).Nonempty) :
    IsDominant (relationChartInclusion H X U V) := by
  have := relationChart_nonempty H X U V hU hV
  exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace (relationChartInclusion H X U V)
    (relationChartInclusion H X U V).isOpenEmbedding.isOpenMap⟩

/-- The first projection from a nonempty relation chart is dominant. -/
theorem relationChartFirst_dominant (hU : (U : Set X.scheme).Nonempty)
    (hV : (V : Set X.scheme).Nonempty) : IsDominant (relationChartFirst H X U V) := by
  have := relationChartInclusion_dominant H X U V hU hV
  have : IsDominant (relationChartFirst H X U V ≫ U.ι) := by
    rw [relationChartFirst_fac]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion (relationChartFirst H X U V) U.ι

/-- The second projection from a nonempty relation chart is dominant. -/
theorem relationChartSecond_dominant (hU : (U : Set X.scheme).Nonempty)
    (hV : (V : Set X.scheme).Nonempty) : IsDominant (relationChartSecond H X U V) := by
  have := relationChartInclusion_dominant H X U V hU hV
  have : IsDominant (relationChartSecond H X U V ≫ V.ι) := by
    rw [relationChartSecond_fac]
    infer_instance
  exact IsDominant.of_comp_of_isOpenImmersion (relationChartSecond H X U V) V.ι

end

end GroupActions.Variety
