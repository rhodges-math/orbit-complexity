import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorCharts

/-! # Descent through the flag quotient

A morphism invariant under right multiplication by the Borel subgroup descends uniquely
through the flag quotient. The descended morphism is obtained from the translated
opposite-unipotent charts.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) (X : GroupActions.Variety K)

omit [IsAlgClosed K] [CharZero K] in
private theorem fibre_constant
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g))
    (g h : G.points) (he : SchubertGeometry.flagProjection G g =
      SchubertGeometry.flagProjection G h) :
    GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g) =
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G h) := by
  have hb : g⁻¹ * h ∈ G.borelPoints :=
    (SchubertGeometry.flagProjection_eq_iff G g h).mp he
  have hg : g * (g⁻¹ * h) = h := by group
  simpa only [Subtype.coe_mk, hg] using (hB g ⟨g⁻¹ * h, hb⟩).symm

private theorem local_compatible
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g))
    (g h : G.points) :
    (SchubertGeometry.flagOverlapInclusion G g h).left ≫
        (SchubertGeometry.flagChartMap G g ≫ f).left =
      ((SchubertGeometry.flagTransition G g h).left ≫
        (SchubertGeometry.flagOverlapInclusion G h g).left) ≫
          (SchubertGeometry.flagChartMap G h ≫ f).left := by
  have he :
      SchubertGeometry.flagOverlapInclusion G g h ≫
          SchubertGeometry.flagChartMap G g ≫ f =
        SchubertGeometry.flagTransition G g h ≫
          SchubertGeometry.flagOverlapInclusion G h g ≫
            SchubertGeometry.flagChartMap G h ≫ f := by
    apply GroupActions.Variety.mapPoints_injective
    funext x
    simp only [GroupActions.Variety.mapPoints_comp, SchubertGeometry.flagChartMap_points]
    apply fibre_constant G X f hB
    exact (SchubertGeometry.flagTransition_flag G g h x).symm
  exact congrArg Over.Hom.left he

private def descendedScheme
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g)) :
    SchubertGeometry.flagScheme G ⟶ X.scheme :=
  Multicoequalizer.desc (SchubertGeometry.flagGlueData G).toGlueData.diagram _
    (fun g => (SchubertGeometry.flagChartMap G g ≫ f).left)
    (fun ij => local_compatible G X f hB ij.1 ij.2)

private theorem descendedScheme_chart
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g))
    (g : G.points) :
    SchubertGeometry.flagSchemeChart G g ≫ descendedScheme G X f hB =
      (SchubertGeometry.flagChartMap G g ≫ f).left := by
  exact Multicoequalizer.π_desc (SchubertGeometry.flagGlueData G).toGlueData.diagram _
    (fun g => (SchubertGeometry.flagChartMap G g ≫ f).left)
    (fun ij => local_compatible G X f hB ij.1 ij.2) g

private theorem descendedScheme_base
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g)) :
    descendedScheme G X f hB ≫ X.toSpec = SchubertGeometry.flagSchemeToSpec G := by
  apply (SchubertGeometry.flagSchemeCover G).hom_ext
  intro g
  change G.points at g
  change SchubertGeometry.flagSchemeChart G g ≫
      (descendedScheme G X f hB ≫ X.toSpec) =
    SchubertGeometry.flagSchemeChart G g ≫ SchubertGeometry.flagSchemeToSpec G
  rw [← Category.assoc, descendedScheme_chart G X f hB g,
    SchubertGeometry.flagSchemeChart_toSpec G g]
  exact (SchubertGeometry.flagChartMap G g ≫ f).w

private def descended
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g)) :
    (SchubertGeometry.flagVariety G).toOver ⟶ X.toOver :=
  Over.homMk (descendedScheme G X f hB) (descendedScheme_base G X f hB)

private theorem descended_chart
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g))
    (g : G.points) :
    SchubertGeometry.flagChartMorphism G g ≫ descended G X f hB =
      SchubertGeometry.flagChartMap G g ≫ f := by
  apply Over.OverMorphism.ext
  exact descendedScheme_chart G X f hB g

private theorem descended_factor
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g)) :
    SchubertGeometry.flagQuotientMorphism G ≫ descended G X f hB = f := by
  apply GroupActions.Variety.mapPoints_injective
  funext z
  obtain ⟨g, rfl⟩ := (GroupActions.reductivePointsMulEquiv G).surjective z
  have hg : GroupActions.Variety.mapPoints (SchubertGeometry.flagChartMap G g) 1 =
      GroupActions.reductivePointsMulEquiv G g := by
    rw [SchubertGeometry.flagChartMap_points]
    simp only [map_one, OneMemClass.coe_one, mul_one]
    rfl
  have hQ := congrArg (fun k => GroupActions.Variety.mapPoints k 1)
    (SchubertGeometry.flagChartMap_quotient G g)
  rw [GroupActions.Variety.mapPoints_comp, hg] at hQ
  have hq := congrArg (fun k => GroupActions.Variety.mapPoints k 1)
    (descended_chart G X f hB g)
  rw [GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_comp, hg] at hq
  rw [GroupActions.Variety.mapPoints_comp, hQ]
  exact hq

/-- Right-Borel-invariant variety morphisms descend uniquely through the flag quotient. -/
theorem flagQuotient_desc
    (f : (GroupActions.reductiveVariety G).toOver ⟶ X.toOver)
    (hB : ∀ (g : G.points) (b : G.borelPoints),
      GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G (g * b)) =
        GroupActions.Variety.mapPoints f (GroupActions.reductivePointsMulEquiv G g)) :
    ∃! q : (SchubertGeometry.flagVariety G).toOver ⟶ X.toOver,
      SchubertGeometry.flagQuotientMorphism G ≫ q = f := by
  refine ⟨descended G X f hB, descended_factor G X f hB, ?_⟩
  intro q hq
  apply Over.OverMorphism.ext
  apply (SchubertGeometry.flagSchemeCover G).hom_ext
  intro g
  change G.points at g
  change (SchubertGeometry.flagChartMorphism G g ≫ q).left =
    (SchubertGeometry.flagChartMorphism G g ≫ descended G X f hB).left
  have he : SchubertGeometry.flagChartMorphism G g ≫ q =
      SchubertGeometry.flagChartMap G g ≫ f := by
    rw [← SchubertGeometry.flagChartMap_quotient G g, Category.assoc, hq]
  exact congrArg Over.Hom.left (he.trans (descended_chart G X f hB g).symm)

end SchubertGeometry
