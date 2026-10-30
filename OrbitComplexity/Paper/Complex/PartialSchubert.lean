import OrbitComplexity.SchubertGeometry.Parabolics.ProjectionActions
import OrbitComplexity.SchubertGeometry.Parabolics.EmptyLevi
import OrbitComplexity.Paper.ToricComplexity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Stabilizers and Levi complexity of partial Schubert varieties

The stabilizer is determined by the longest parabolic suffix. A Levi subgroup contained
in that stabilizer acts on the partial Schubert variety, and the projection preserves
complexity when it also acts on the full Schubert variety.
-/

noncomputable section
namespace SchubertOrbits
open CategoryTheory GroupActions ReductiveGroups SchubertGeometry
open scoped Pointwise
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The complex partial Schubert stabilizer is the parabolic of the longest suffix descents. -/
theorem partial_schubert_stabilizer_complex (G : ReductiveGroupData ℂ)
    (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    MulAction.stabilizer G.points ((partialFlagPointsEquiv G J) ⁻¹'
      Set.range (Variety.mapPoints (partialSchubertInclusion G J w))) =
        standardParabolicPoints G (BruhatIntervals.leftDescents
          (weylCoxeterSystem G.rootBase) (w * longestParabolicElement G.rootBase J)) :=
  partialSchubertStabilizer_eq G J w hw

/-- Stabilizing Levi subgroups act regularly; a common Levi action preserves complexity.
For an empty set of simple roots the Levi is the torus and the equality always applies. -/
theorem partial_schubert_levi (G : ReductiveGroupData K) (I J : Set G.rootBase.support)
    (w : G.weylGroup) (hw : IsMinimalRightParabolic G.rootBase J w)
    (hTop : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J)) :
  (∃ a : ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver,
    letI := a
    IsModHom (leviVariety G I).toOver (partialSchubertInclusion G J w) ∧
    ((∃ b : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := b
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
        I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    ∀ hFull : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w,
      letI := schubertLeviAction G I w hFull
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (schubertVariety G w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (partialSchubertVariety G J w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver)
      complexity (leviGroupData G I) (partialSchubertVariety G J w) =
        complexity (leviGroupData G I) (schubertVariety G w)) ∧
  (G.leviPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  G.leviBorelPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support)) ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support) ≫
    leviBorelLeviInclusion G (∅ : Set G.rootBase.support))) ∧
  (letI := schubertLeviAction G ∅ w (Set.empty_subset _)
   letI := partialSchubertLeviAction G ∅ J w hw (Set.empty_subset _)
   letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
       (schubertVariety G w).toOver :=
     inferInstanceAs (ModObj (leviVariety G ∅).toOver (schubertVariety G w).toOver)
   letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
       (partialSchubertVariety G J w).toOver :=
     inferInstanceAs (ModObj (leviVariety G ∅).toOver (partialSchubertVariety G J w).toOver)
   complexity (leviGroupData G ∅) (partialSchubertVariety G J w) =
     complexity (leviGroupData G ∅) (schubertVariety G w)) := by
  refine ⟨⟨partialSchubertLeviAction G I J w hw hTop,
    partialSchubertLeviEquivariant G I J w hw hTop, levi_schubert_action_iff G I w,
    ?_⟩, emptyLevi_isTorus G, ?_⟩
  · intro hFull
    exact partial_schubert_complexity G I J w hw hTop hFull
  · exact partial_schubert_complexity G ∅ J w hw (Set.empty_subset _) (Set.empty_subset _)

/-- The Levi action and complexity statements, including the torus case, over the complex field. -/
theorem partial_schubert_levi_complex (G : ReductiveGroupData ℂ)
    (I J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (hTop : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase)
      (w * longestParabolicElement G.rootBase J)) :
  (∃ a : ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver,
    letI := a
    IsModHom (leviVariety G I).toOver (partialSchubertInclusion G J w) ∧
    ((∃ b : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := b
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) ↔
        I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w) ∧
    ∀ hFull : I ⊆ BruhatIntervals.leftDescents (weylCoxeterSystem G.rootBase) w,
      letI := schubertLeviAction G I w hFull
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (schubertVariety G w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
      letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
          (partialSchubertVariety G J w).toOver :=
        inferInstanceAs (ModObj (leviVariety G I).toOver (partialSchubertVariety G J w).toOver)
      complexity (leviGroupData G I) (partialSchubertVariety G J w) =
        complexity (leviGroupData G I) (schubertVariety G w)) ∧
  (G.leviPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  G.leviBorelPoints (∅ : Set G.rootBase.support) = G.torusPoints ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support)) ∧
  IsIso (torusLeviBorelInclusion G (∅ : Set G.rootBase.support) ≫
    leviBorelLeviInclusion G (∅ : Set G.rootBase.support))) ∧
  (letI := schubertLeviAction G ∅ w (Set.empty_subset _)
   letI := partialSchubertLeviAction G ∅ J w hw (Set.empty_subset _)
   letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
       (schubertVariety G w).toOver :=
     inferInstanceAs (ModObj (leviVariety G ∅).toOver (schubertVariety G w).toOver)
   letI : ModObj (reductiveVariety (leviGroupData G ∅)).toOver
       (partialSchubertVariety G J w).toOver :=
     inferInstanceAs (ModObj (leviVariety G ∅).toOver (partialSchubertVariety G J w).toOver)
   complexity (leviGroupData G ∅) (partialSchubertVariety G J w) =
     complexity (leviGroupData G ∅) (schubertVariety G w)) :=
  partial_schubert_levi G I J w hw hTop


/-- Partial and full Schubert complexities agree over the complex numbers;
toricity is equivalent to distinct reduced letters and to length equalling support. -/
theorem partial_schubert_toric_complex (G : ReductiveGroupData ℂ)
    (J : Set G.rootBase.support) (w : G.weylGroup)
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
          BruhatIntervals.supportCard (weylCoxeterSystem G.rootBase) w) :=
  @partial_schubert_toric.{0} ℂ
    (inferInstanceAs (Field ℂ)) (inferInstanceAs (IsAlgClosed ℂ))
    (inferInstanceAs (CharZero ℂ)) G J w hw

end SchubertOrbits
