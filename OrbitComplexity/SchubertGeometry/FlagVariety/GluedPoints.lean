import OrbitComplexity.SchubertGeometry.FlagVariety.Gluing

/-!
# Rational points of the glued flag scheme

Rational sections of the glued scheme lift to its unipotent charts. The overlap pullback
identifies equal chart sections with equal Borel cosets, giving the rational-point
identification of the glued scheme with the flag space.

## Main definitions

* `SchubertGeometry.flagSchemePoints`: rational sections of the glued scheme.
* `SchubertGeometry.flagSchemePointsEquiv`: rational flags as glued scheme points.

## Main results

* `SchubertGeometry.flagSchemeChartPoints_eq_iff`: equality of chart representatives.
* `SchubertGeometry.flagSchemePointsEquiv_chart`: compatibility with chart sections.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- Rational sections of the glued flag scheme over its base field. -/
abbrev flagSchemePoints :=
  {p : Spec (CommRingCat.of K) ⟶ flagScheme G // p ≫ flagSchemeToSpec G = 𝟙 _}

/-- A rational unipotent chart point defines a rational point of the glued flag scheme. -/
def flagSchemeChartPoints (g : G.points)
    (u : (GroupActions.oppositeUnipotentVariety G).points) : flagSchemePoints G :=
  ⟨u.val ≫ flagSchemeChart G g, by
    rw [Category.assoc, flagSchemeChart_toSpec]
    exact u.property⟩

/-- Every rational point of the glued flag scheme is represented in a unipotent chart. -/
theorem flagSchemePoints_chart (z : flagSchemePoints G) :
    ∃ (g : G.points) (u : (GroupActions.oppositeUnipotentVariety G).points),
      flagSchemeChartPoints G g u = z := by
  obtain ⟨g, ⟨l, hl⟩, he⟩ :=
    GroupActions.point_factors_glued (flagGlueData G) (flagSchemeToSpec G) z
  change G.points at g
  change Spec (CommRingCat.of K) ⟶ (GroupActions.oppositeUnipotentVariety G).scheme at l
  have hbase : l ≫ (GroupActions.oppositeUnipotentVariety G).toSpec = 𝟙 _ := by
    change l ≫ flagSchemeChart G g ≫ flagSchemeToSpec G = 𝟙 _ at hl
    rwa [flagSchemeChart_toSpec] at hl
  exact ⟨g, ⟨l, hbase⟩, Subtype.ext he⟩

private theorem chartPoints_flag (g h : G.points)
    (u v : (GroupActions.oppositeUnipotentVariety G).points)
    (he : flagSchemeChartPoints G g u = flagSchemeChartPoints G h v) :
    flagChartPoint G g u = flagChartPoint G h v := by
  have he' : u.val ≫ flagSchemeChart G g = v.val ≫ flagSchemeChart G h :=
    congrArg Subtype.val he
  let l : Spec (CommRingCat.of K) ⟶ (flagOverlapVariety G g h).scheme :=
    PullbackCone.IsLimit.lift ((flagGlueData G).vPullbackConeIsLimit g h) u.val v.val he'
  have h₁ : l ≫ (flagOverlapInclusion G g h).left = u.val :=
    PullbackCone.IsLimit.lift_fst _ _ _ _
  have h₂ : l ≫ ((flagTransition G g h).left ≫ (flagOverlapInclusion G h g).left) = v.val :=
    PullbackCone.IsLimit.lift_snd _ _ _ _
  have hbase : l ≫ (flagOverlapVariety G g h).toSpec = 𝟙 _ := by
    have hb : (flagOverlapInclusion G g h).left ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec =
      (flagOverlapVariety G g h).toSpec := (flagOverlapInclusion G g h).w
    rw [← hb, ← Category.assoc, h₁]
    exact u.property
  let x : (flagOverlapVariety G g h).points := ⟨l, hbase⟩
  have hu : GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) x = u :=
    Subtype.ext h₁
  have hv : GroupActions.Variety.mapPoints (flagOverlapInclusion G h g)
      (GroupActions.Variety.mapPoints (flagTransition G g h) x) = v := by
    apply Subtype.ext
    exact (Category.assoc _ _ _).trans h₂
  rw [← hu, ← hv]
  exact (flagTransition_flag G g h x).symm

private theorem chartPoints_eq (g h : G.points)
    (u v : (GroupActions.oppositeUnipotentVariety G).points)
    (he : flagChartPoint G g u = flagChartPoint G h v) :
    flagSchemeChartPoints G g u = flagSchemeChartPoints G h v := by
  have hu : u ∈ Set.range (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h)) := by
    rw [GroupActions.Variety.range_mapPoints]
    change _ ∈ Set.range
      (((GroupActions.oppositeUnipotentVariety G).openInclusion (flagOverlap G g h)).left)
    rw [GroupActions.Variety.openInclusion_range]
    exact mem_flagOverlap_of_flag G g h u v he
  obtain ⟨x, hx⟩ := hu
  have hv : GroupActions.Variety.mapPoints (flagOverlapInclusion G h g)
      (GroupActions.Variety.mapPoints (flagTransition G g h) x) = v := by
    apply flagChartPoint_injective G h
    rw [flagTransition_flag, hx]
    exact he
  have hx' : x.val ≫ (flagOverlapInclusion G g h).left = u.val :=
    congrArg Subtype.val hx
  have hv' : (x.val ≫ (flagTransition G g h).left) ≫
      (flagOverlapInclusion G h g).left = v.val := congrArg Subtype.val hv
  have hc : (flagTransition G g h).left ≫ (flagOverlapInclusion G h g).left ≫
      flagSchemeChart G h = (flagOverlapInclusion G g h).left ≫ flagSchemeChart G g :=
    (flagGlueData G).glue_condition g h
  apply Subtype.ext
  change u.val ≫ flagSchemeChart G g = v.val ≫ flagSchemeChart G h
  rw [← hx', ← hv']
  simpa only [Category.assoc] using congrArg (fun f => x.val ≫ f) hc.symm

/-- Two rational chart representatives agree exactly when they represent the same flag coset. -/
theorem flagSchemeChartPoints_eq_iff (g h : G.points)
    (u v : (GroupActions.oppositeUnipotentVariety G).points) :
    flagSchemeChartPoints G g u = flagSchemeChartPoints G h v ↔
      flagChartPoint G g u = flagChartPoint G h v :=
  ⟨chartPoints_flag G g h u v, chartPoints_eq G g h u v⟩

private theorem chartOneFlag (g : G.points) :
    flagChartPoint G g 1 = flagProjection G g := by
  simp only [flagChartPoint, map_one, OneMemClass.coe_one, mul_one]

private def cosetSection : flagPoints G → flagSchemePoints G :=
  Quotient.lift (fun g => flagSchemeChartPoints G g 1) (fun g h he =>
    chartPoints_eq G g h 1 1 (by
      rw [chartOneFlag, chartOneFlag]
      exact Quotient.sound he))

private theorem cosetSection_injective : Function.Injective (cosetSection G) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro g h he
  change flagSchemeChartPoints G g 1 = flagSchemeChartPoints G h 1 at he
  have hflag := chartPoints_flag G g h 1 1 he
  simpa only [chartOneFlag] using hflag

private theorem cosetSection_surjective : Function.Surjective (cosetSection G) := by
  intro z
  obtain ⟨g, u, hu⟩ := flagSchemePoints_chart G z
  refine ⟨flagProjection G
    (g * (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points)), ?_⟩
  change flagSchemeChartPoints G
    (g * (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points)) 1 = z
  rw [← hu]
  apply chartPoints_eq
  rw [chartOneFlag]
  rfl

/-- Rational points of the glued flag scheme are the Borel cosets of group points. -/
def flagSchemePointsEquiv : flagPoints G ≃ flagSchemePoints G :=
  Equiv.ofBijective (cosetSection G) ⟨cosetSection_injective G, cosetSection_surjective G⟩

/-- The coset identification maps chart coordinates to their glued rational section. -/
theorem flagSchemePointsEquiv_chart (g : G.points)
    (u : (GroupActions.oppositeUnipotentVariety G).points) :
    flagSchemePointsEquiv G (flagChartPoint G g u) = flagSchemeChartPoints G g u := by
  change flagSchemeChartPoints G
    (g * (GroupActions.oppositeUnipotentPointsMulEquiv G u : G.points)) 1 =
      flagSchemeChartPoints G g u
  apply chartPoints_eq
  rw [chartOneFlag]
  rfl

end
end SchubertGeometry
