import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

/-! # Transitions of the local Borel torsor charts

The Borel factor of a change of unipotent coordinates multiplies the fibre coordinate
on the left. These factors satisfy the cocycle identity on triple intersections.

## Main results

* `SchubertGeometry.flagTorsor_section`: local sections differ by the Borel transition.
* `SchubertGeometry.flagTorsor_transition`: local product charts have compatible group images.
* `SchubertGeometry.flagTorsor_cocycle`: transition factors compose on triple overlaps.
-/

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

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

/-- On overlapping flag charts, the section changes by the Borel transition factor. -/
theorem flagTorsor_section (g h : G.points) :
    flagOverlapInclusion G g h ≫ flagChartMap G g =
      (flagOverlapCoordinate G g h ≫ flagChartMap G h) *
        (flagOverlapBorel G g h ≫ GroupActions.borelInclusion G) := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  rw [mapPoints_mul]
  simp only [GroupActions.Variety.mapPoints_comp, flagChartMap_points,
    GroupActions.borelInclusion_points]
  change (GroupActions.reductivePointsMulEquiv G) _ =
    (GroupActions.reductivePointsMulEquiv G) _ * (GroupActions.reductivePointsMulEquiv G) _
  rw [← (GroupActions.reductivePointsMulEquiv G).map_mul]
  apply congrArg (GroupActions.reductivePointsEquiv G)
  have hf := flagOverlap_factor G g h p
  calc
    _ = h * ((h⁻¹ * g) *
        (GroupActions.oppositeUnipotentPointsMulEquiv G
          (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h) p) : G.points)) := by
      group
    _ = _ := by rw [hf]; group

/-- Changing the unipotent chart multiplies the Borel coordinate by its transition factor. -/
theorem flagTorsor_transition (g h : G.points)
    (Z : Over (Spec (CommRingCat.of K)))
    (x : Z ⟶ (flagOverlapVariety G g h).toOver)
    (b : Z ⟶ (GroupActions.borelVariety G).toOver) :
    lift (x ≫ flagOverlapInclusion G g h) b ≫ (flagTorsorIso G g).hom ≫
        pullback.snd (flagChartMorphism G g) (flagQuotientMorphism G) =
      lift (x ≫ flagOverlapCoordinate G g h) ((x ≫ flagOverlapBorel G g h) * b) ≫
        (flagTorsorIso G h).hom ≫
          pullback.snd (flagChartMorphism G h) (flagQuotientMorphism G) := by
  simp only [flagTorsorIso_group, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
    MonObj.mul_comp]
  rw [Category.assoc x (flagOverlapInclusion G g h), flagTorsor_section,
    MonObj.comp_mul]
  simp only [Category.assoc, mul_assoc]

private theorem triple_last (g h k : G.points) :
    flagTripleCoordinate G g h k ≫ flagOverlapCoordinate G h k =
      flagTripleSnd G g h k ≫ flagOverlapCoordinate G g k := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  apply flagChartPoint_injective G k
  simp only [GroupActions.Variety.mapPoints_comp]
  rw [← flagOverlapCoordinate_flag, ← flagOverlapCoordinate_flag]
  have hc := congrArg (fun f => GroupActions.Variety.mapPoints f p)
    (flagTripleCoordinate_comp G g h k)
  simp only [GroupActions.Variety.mapPoints_comp] at hc
  rw [hc, flagTransition_flag]
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f p)
    (flagTriple_condition G g h k)
  simp only [GroupActions.Variety.mapPoints_comp] at he
  rw [he]

/-- Borel transition factors satisfy the cocycle identity in their multiplication order. -/
theorem flagTorsor_cocycle (g h k : G.points) :
    flagTripleSnd G g h k ≫ flagOverlapBorel G g k =
      (flagTripleCoordinate G g h k ≫ flagOverlapBorel G h k) *
        (flagTripleFst G g h k ≫ flagOverlapBorel G g h) := by
  have : Mono (GroupActions.borelInclusion G) :=
    Over.mono_of_mono_left (GroupActions.borelInclusion G)
  apply (cancel_mono (GroupActions.borelInclusion G)).mp
  rw [MonObj.mul_comp]
  apply mul_left_cancel (a := flagTripleSnd G g h k ≫
    flagOverlapCoordinate G g k ≫ flagChartMap G k)
  have hgh := congrArg (fun f => flagTripleFst G g h k ≫ f) (flagTorsor_section G g h)
  have hgk := congrArg (fun f => flagTripleSnd G g h k ≫ f) (flagTorsor_section G g k)
  have hhk := congrArg (fun f => flagTripleCoordinate G g h k ≫ f)
    (flagTorsor_section G h k)
  simp only [MonObj.comp_mul, Category.assoc] at hgh hgk hhk ⊢
  have hu := congrArg (fun f => f ≫ flagChartMap G g) (flagTriple_condition G g h k)
  have hv₀ := congrArg (fun f => f ≫ flagChartMap G h)
    (flagTripleCoordinate_comp G g h k)
  have ht := congrArg (fun f => flagTripleFst G g h k ≫ f ≫ flagChartMap G h)
    (flagTransition_comp G g h)
  have hw := congrArg (fun f => f ≫ flagChartMap G k) (triple_last G g h k)
  simp only [Category.assoc] at hu hv₀ ht hw
  have hv := hv₀.trans ht
  calc
    _ = flagTripleSnd G g h k ≫ flagOverlapInclusion G g k ≫ flagChartMap G g := hgk.symm
    _ = flagTripleFst G g h k ≫ flagOverlapInclusion G g h ≫ flagChartMap G g := hu.symm
    _ = _ := hgh
    _ = (flagTripleCoordinate G g h k ≫ flagOverlapInclusion G h k ≫ flagChartMap G h) *
        (flagTripleFst G g h k ≫ flagOverlapBorel G g h ≫ GroupActions.borelInclusion G) := by
      rw [hv]
    _ = _ := by rw [hhk, hw, mul_assoc]

end
end SchubertGeometry
