import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoefficient
import OrbitComplexity.SchubertGeometry.Cells.Stability
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The two cells in a translated transverse chart

The zero additive coordinate lies in the corresponding simple opposite
cell. A nonzero coordinate lies in the identity opposite cell, by the
rank-one Gauss factorization.
-/

open ReductiveGroups ReductiveGroups.RankOne TauCeti GroupActions

noncomputable section

namespace SchubertGeometry.DeterminantSection

open private SchubertGeometry.DeterminantSection.translated_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoefficient
open private SchubertGeometry.DeterminantSection.negative_mem from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Gauss
open private SchubertGeometry.flagProjection_borel from
  OrbitComplexity.SchubertGeometry.FlagVariety.QuotientCharts

private theorem inverse_root_gauss {M F : Type*} [Group M] [Field F]
    (B T U : Subgroup M) (x y : F → M) (r : M)
    (h : IsRankOneBruhatData B T x y r) (hy : ∀ t : F, y t ∈ U)
    (t : F) (ht : t ≠ 0) :
    ∃ u ∈ U, ∃ b ∈ B, x t * r⁻¹ = u * b := by
  obtain ⟨b, hb, hfactor⟩ := h.x_mul_self_mem ht
  refine ⟨y t⁻¹, hy _, b * (r * r)⁻¹,
    B.mul_mem hb (h.torus_le (T.inv_mem h.sq_mem)), ?_⟩
  calc
    _ = (x t * r) * (r * r)⁻¹ := by group
    _ = (y t⁻¹ * b) * (r * r)⁻¹ := congrArg (· * (r * r)⁻¹) hfactor
    _ = _ := mul_assoc _ _ _

private theorem translated_zero {M : Type*} [Group M]
    (w c h u x : M) (hh : h = c * w⁻¹) (hx : x = 1) :
    h * (w * (u * x) * w⁻¹) = (c * u * c⁻¹) * h := by
  rw [hh, hx]
  group

private theorem multiply_gauss {M : Type*} [Group M]
    (c x r b v d : M) (h : x * r = v * d) :
    c * ((x * r) * b) = (c * v) * (d * b) := by
  rw [h]
  group

private theorem sign_ne_zero {K : Type*} [Field K]
    (ε : K) (hε : ε = 1 ∨ ε = -1) : ε ≠ 0 := by
  rcases hε with rfl | rfl <;> simp

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

private theorem opposite_orbit (w : G.weylGroup) (u : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) :
    flagVarietyPointsEquiv G (flagProjection G (u * G.weylPoint w)) ∈
      Set.range (Variety.mapPoints (X := oppositeSchubertCell G w) (Y := flagVariety G)
        (oppositeSchubertCellInclusion G w)) := by
  let ub : G.oppositeBorelPoints := ⟨u, G.oppositeUnipotent_le_oppositeBorel hu⟩
  let b : (oppositeBorelVariety G).points := (oppositeBorelPointsMulEquiv G).symm ub
  have hb : (oppositeBorelPointsMulEquiv G b : G.points) = u :=
    congrArg Subtype.val ((oppositeBorelPointsMulEquiv G).apply_symm_apply ub)
  apply (Set.ext_iff.mp (oppositeSchubertCell_points_range G w) _).mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨b, ?_⟩
  exact (oppositeBorelFlag_smul G b (flagProjection G (G.weylPoint w))).trans
    ((congrArg (fun p : G.points => flagVarietyPointsEquiv G
      (p • flagProjection G (G.weylPoint w))) hb).trans
        (congrArg (flagVarietyPointsEquiv G) (flagProjection_smul G u (G.weylPoint w))).symm)

private theorem orbit_flag (w : G.weylGroup) (u : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) (g : G.points)
    (hg : flagProjection G g = flagProjection G (G.weylPoint w)) :
    flagVarietyPointsEquiv G (flagProjection G (u * g)) ∈
      Set.range (Variety.mapPoints (X := oppositeSchubertCell G w) (Y := flagVariety G)
        (oppositeSchubertCellInclusion G w)) := by
  have h := (flagProjection_smul G u g).trans
    ((congrArg (fun q : flagPoints G => u • q) hg).trans
      (flagProjection_smul G u (G.weylPoint w)).symm)
  exact (congrArg (flagVarietyPointsEquiv G) h).symm ▸ opposite_orbit G w u hu

/-- The zero transverse coordinate lies in the corresponding simple opposite cell. -/
theorem oppositionRootLift_zero_cell (i : G.rootBase.support) (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) :
    flagVarietyPointsEquiv G (flagProjection G (oppositionRootLift G i u 0)) ∈
      Set.range (Variety.mapPoints
        (X := oppositeSchubertCell G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G
          i)))
        (Y := flagVariety G)
        (oppositeSchubertCellInclusion G
          (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i)))) := by
  have hzero : oppositionRootLift G i u 0 =
      (oppositionConjugator G i * u * (oppositionConjugator G i)⁻¹) * oppositionChartPoint G i :=
    translated_zero G.longestPoint (oppositionConjugator G i) (oppositionChartPoint G i) u
      (gaParameterPoint (G.simpleRootMap i) (0 : K)) rfl (gaParameterPoint_zero _)
  have hmem := orbit_flag G (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))
    (oppositionConjugator G i * u * (oppositionConjugator G i)⁻¹)
    (oppositionComplement_mem G i u hu) (oppositionChartPoint G i) (oppositionChartPoint_flag G i)
  exact (congrArg (fun p : G.points => flagVarietyPointsEquiv G (flagProjection G p)) hzero).symm ▸
    hmem

/-- Every nonzero transverse coordinate belongs to the identity opposite cell. -/
theorem oppositionRootLift_ne_zero_cell (i : G.rootBase.support) (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i)}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
        (RootPairing.weylGroup.ofIdx G.rootSystem i))) (t : K) (ht : t ≠ 0) :
    flagVarietyPointsEquiv G (flagProjection G (oppositionRootLift G i u t)) ∈
      Set.range (Variety.mapPoints (X := oppositeSchubertCell G 1) (Y := flagVariety G)
        (oppositeSchubertCellInclusion G 1)) := by
  obtain ⟨ε, hε, hparameter⟩ := oppositionSimple_parameter G i
  obtain ⟨b, hb, hchart⟩ := oppositionChartPoint_torus G i
  obtain ⟨v, hv, d, hd, hgauss⟩ := inverse_root_gauss
    G.borelPoints G.torusPoints G.oppositeUnipotentPoints
    (fun z : K => gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) z)
    (fun z : K => gaParameterPoint (G.negativeSimpleRootMap (oppositionSimple G i)) z)
    (G.reflectionPoint (oppositionSimple G i).val)
    (G.isBruhatSystem.rankOne (oppositionSimple G i))
    (fun z => SchubertGeometry.DeterminantSection.negative_mem G (oppositionSimple G i) z)
    (ε * t) (mul_ne_zero (sign_ne_zero ε hε) ht)
  let c : G.points := oppositionConjugator G i * u * (oppositionConjugator G i)⁻¹
  have hc : c ∈ G.oppositeUnipotentPoints := oppositionComplement_mem G i u hu
  have hfactor := SchubertGeometry.DeterminantSection.translated_factor G.longestPoint
    (oppositionConjugator G i) u (gaParameterPoint (G.simpleRootMap i) t)
    (gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t))
    (G.reflectionPoint (oppositionSimple G i).val)⁻¹ b (hparameter t) hchart
  have hfull : oppositionRootLift G i u t = (c * v) * (d * b) :=
    hfactor.trans (multiply_gauss c
      (gaParameterPoint (G.simpleRootMap (oppositionSimple G i)) (ε * t))
      (G.reflectionPoint (oppositionSimple G i).val)⁻¹ b v d hgauss)
  have hproj : flagProjection G (oppositionRootLift G i u t) = flagProjection G (c * v) :=
    (congrArg (flagProjection G) hfull).trans
      (SchubertGeometry.flagProjection_borel G (c * v)
        ⟨d * b, G.borelPoints.mul_mem hd (G.torus_le_borel hb)⟩)
  have hweyl : G.weylPoint (1 : G.weylGroup) = 1 := by
    rw [G.weylPoint_eq, weylElementPoint_one]
  have hmem := opposite_orbit G 1 (c * v) (G.oppositeUnipotentPoints.mul_mem hc hv)
  have heq := congrArg (fun p : G.points => flagVarietyPointsEquiv G (flagProjection G p))
    ((congrArg (fun p : G.points => (c * v) * p) hweyl).trans (mul_one (c * v)))
  exact (congrArg (flagVarietyPointsEquiv G) hproj).symm ▸ (heq ▸ hmem)

end SchubertGeometry.DeterminantSection
