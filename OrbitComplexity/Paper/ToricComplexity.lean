import OrbitComplexity.Paper.RichardsonComplexity
import OrbitComplexity.Paper.IntervalPolytopes
import OrbitComplexity.BruhatIntervals.Graph.ToricMaxima
import OrbitComplexity.BruhatIntervals.Words.Distinct
import OrbitComplexity.SchubertGeometry.Parabolics.TorusActions
import OrbitComplexity.SchubertGeometry.Normality.PositiveResolutionFibres
import OrbitComplexity.SchubertGeometry.Normality.PartialNormalDescent

/-! # Toric varieties and interval dimension

The complexity formulas and normality give the toric Richardson criterion and
the attained upper-interval maximum. Partial Schubert complexity is determined
by the simple letters in a reduced word.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Proposition 7.12.
-/

open ReductiveGroups GroupActions SchubertGeometry BruhatIntervals
noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
  (G : ReductiveGroupData K)

/-- A Richardson variety has zero torus complexity exactly when its interval is toric. -/
theorem richardson_zero_iff_toric (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    torusComplexity G (richardsonVariety G a b) = 0 ↔
      IsToricInterval (weylRealization G.rootBase) a b := by
  rw [richardson_torus_complexity G a b hle]
  change _ ↔ algebraicDim (weylRealization G.rootBase) a b =
    (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a
  have hbound := algebraicDim_le_length (weylRealization G.rootBase) a b hle
  omega

/-- The largest upper-interval length with zero Richardson complexity is attained. -/
theorem richardson_zero_maximum (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
      torusComplexity G (richardsonVariety G w b) = 0 ∧
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) a b) := by
  have h := (toric_interval_maxima (weylRealization G.rootBase) a b hle).2.1
  constructor
  · obtain ⟨w, hw, htoric, hlength⟩ := h.1
    exact ⟨w, hw, (richardson_zero_iff_toric G w b hw.2).mpr htoric, hlength⟩
  · rintro n ⟨w, hw, hzero, hlength⟩
    exact h.2 ⟨w, hw, (richardson_zero_iff_toric G w b hw.2).mp hzero, hlength⟩

private theorem richardson_toric_zero (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsToricVariety G (richardsonVariety G a b) ↔
      torusComplexity G (richardsonVariety G a b) = 0 := by
  have hab : WeylBruhatLE G.rootBase a b :=
    (weyl_bruhat_iff G.rootBase a b).mpr hle
  let := richardsonVariety_integral G a b hab
  exact ⟨fun h ↦ h.2.2,
    fun h ↦ ⟨inferInstance, richardson_normal_stalks G a b hab, h⟩⟩

/-- A complex Richardson variety is toric exactly when its interval polytope has full dimension. -/
theorem richardson_toric_polytope (G : ReductiveGroupData ℂ)
    (a b : G.weylGroup) (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsToricVariety G (richardsonVariety G a b) ↔
      (affineSpan ℝ (intervalPolytope (weylRealization G.rootBase) a b
        (realTwoRho G.rootBase))).finDim =
      (((weylCoxeterSystem G.rootBase).length b -
        (weylCoxeterSystem G.rootBase).length a : ℕ) : WithBot ℕ) := by
  have hiff : IsToricVariety G (richardsonVariety G a b) ↔
      algebraicDim (weylRealization G.rootBase) a b =
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a := by
    rw [@richardson_toric_zero ℂ inferInstance inferInstance inferInstance G a b hle,
      richardson_torus_complexity_complex G a b hle]
    have hbound := algebraicDim_le_length (weylRealization G.rootBase) a b hle
    omega
  rw [(interval_polytope_span_dimension G.rootBase a b hle).2]
  constructor
  · intro h
    exact_mod_cast hiff.mp h
  · intro h
    apply hiff.mpr
    exact_mod_cast h

/-- A Bruhat interval is toric exactly when its Richardson variety is toric. -/
theorem richardson_toric_criterion (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsToricInterval (weylRealization G.rootBase) a b ↔
      IsToricVariety G (richardsonVariety G a b) :=
  (richardson_zero_iff_toric G a b hle).symm.trans
    (richardson_toric_zero G a b hle).symm

/-- The toric interval criterion for complex Richardson varieties. -/
theorem richardson_toric_criterion_complex (G : ReductiveGroupData ℂ)
    (a b : G.weylGroup) (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsToricInterval (weylRealization G.rootBase) a b ↔
      IsToricVariety G (richardsonVariety G a b) := by
  have hdim : IsToricInterval (weylRealization G.rootBase) a b ↔
      (affineSpan ℝ (intervalPolytope (weylRealization G.rootBase) a b
        (realTwoRho G.rootBase))).finDim =
      (((weylCoxeterSystem G.rootBase).length b -
        (weylCoxeterSystem G.rootBase).length a : ℕ) : WithBot ℕ) := by
    rw [(interval_polytope_span_dimension G.rootBase a b hle).2]
    constructor
    · intro h
      change algebraicDim (weylRealization G.rootBase) a b = _ at h
      exact_mod_cast h
    · intro h
      change algebraicDim (weylRealization G.rootBase) a b = _
      exact_mod_cast h
  exact hdim.trans (richardson_toric_polytope G a b hle).symm

/-- Interval dimension is the attained maximum length of a toric upper Richardson variety. -/
theorem richardson_toric_maximum (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
      IsToricVariety G (richardsonVariety G w b) ∧
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) a b) := by
  have h := richardson_zero_maximum G a b hle
  constructor
  · obtain ⟨w, hw, hzero, hlength⟩ := h.1
    exact ⟨w, hw, (richardson_toric_zero G w b hw.2).mpr hzero, hlength⟩
  · rintro n ⟨w, hw, htoric, hlength⟩
    exact h.2 ⟨w, hw, (richardson_toric_zero G w b hw.2).mp htoric, hlength⟩

/-- The attained toric upper-interval maximum over the complex numbers. -/
theorem richardson_toric_maximum_complex (G : ReductiveGroupData ℂ)
    (a b : G.weylGroup) (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
      IsToricVariety G (richardsonVariety G w b) ∧
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) a b) := by
  have h := (toric_interval_maxima (weylRealization G.rootBase) a b hle).2.1
  constructor
  · obtain ⟨w, hw, htoric, hlength⟩ := h.1
    exact ⟨w, hw, (richardson_toric_criterion_complex G w b hw.2).mp htoric, hlength⟩
  · rintro n ⟨w, hw, htoric, hlength⟩
    exact h.2 ⟨w, hw, (richardson_toric_criterion_complex G w b hw.2).mpr htoric, hlength⟩

/-- Richardson torus complexity and the toric upper-interval maximum. -/
theorem richardson_complexity_and_max (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    torusComplexity G (richardsonVariety G a b) =
      (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a -
        algebraicDim (weylRealization G.rootBase) a b ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
      IsToricVariety G (richardsonVariety G w b) ∧
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) a b) :=
  ⟨richardson_torus_complexity G a b hle, richardson_toric_maximum G a b hle⟩

/-- The Richardson complexity formula and toric maximum over the complex numbers. -/
theorem richardson_complexity_and_max_complex (G : ReductiveGroupData ℂ)
    (a b : G.weylGroup) (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    torusComplexity G (richardsonVariety G a b) =
      (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length a -
        algebraicDim (weylRealization G.rootBase) a b ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
      IsToricVariety G (richardsonVariety G w b) ∧
        (weylCoxeterSystem G.rootBase).length b - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) a b) :=
  ⟨richardson_torus_complexity_complex G a b hle,
    richardson_toric_maximum_complex G a b hle⟩

/-- Zero partial Schubert complexity means equal length and support and distinct reduced words. -/
theorem partial_torus_zero_iff (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    letI := partialSchubertTorusAction G J w hw
    (torusComplexity G (partialSchubertVariety G J w) = 0 ↔
      (weylCoxeterSystem G.rootBase).length w =
        supportCard (weylCoxeterSystem G.rootBase) w) ∧
    (torusComplexity G (partialSchubertVariety G J w) = 0 ↔
      ∀ word : List G.rootBase.support, (weylCoxeterSystem G.rootBase).IsReduced word →
        (weylCoxeterSystem G.rootBase).wordProd word = w →
          (word.map (weylCoxeterSystem G.rootBase).simple).Nodup) := by
  let := partialSchubertTorusAction G J w hw
  rw [partial_torus_complexity G J w hw, schubert_torus_complexity G w]
  have h := distinct_reduced_words (weylCoxeterSystem G.rootBase) w
  exact ⟨h.1, h.1.trans h.2⟩

/-- Partial and full Schubert complexities agree, and toricity is equivalent
to distinct reduced letters and to equality of length and support. -/
theorem partial_schubert_toric (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    letI := partialSchubertTorusAction G J w hw
    torusComplexity G (partialSchubertVariety G J w) =
        torusComplexity G (schubertVariety G w) ∧
      (IsToricVariety G (partialSchubertVariety G J w) ↔
        ∀ word : List G.rootBase.support,
          (weylCoxeterSystem G.rootBase).IsReduced word →
          (weylCoxeterSystem G.rootBase).wordProd word = w →
            (word.map (weylCoxeterSystem G.rootBase).simple).Nodup) ∧
      (IsToricVariety G (partialSchubertVariety G J w) ↔
        (weylCoxeterSystem G.rootBase).length w =
          supportCard (weylCoxeterSystem G.rootBase) w) := by
  let := partialSchubertTorusAction G J w hw
  have hnormal : (partialSchubertVariety G J w).IsNormal :=
    @partialSchubert_normal_stalks.{u} K kField kClosed kZero G J w hw
  have htoric : IsToricVariety G (partialSchubertVariety G J w) ↔
      torusComplexity G (partialSchubertVariety G J w) = 0 :=
    ⟨fun h => h.2.2, fun h => ⟨inferInstance, hnormal, h⟩⟩
  have hzero := partial_torus_zero_iff G J w hw
  exact ⟨partial_torus_complexity G J w hw,
    htoric.trans hzero.2, htoric.trans hzero.1⟩

end SchubertOrbits
