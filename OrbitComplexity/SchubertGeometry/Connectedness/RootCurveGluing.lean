import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.RootCurveOverlap
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoCharts
import Mathlib.AlgebraicGeometry.Gluing

/-! # Gluing the two arbitrary-root charts

The gluing construction is proved for arbitrary varieties and open charts before it is
applied to the standard projective line. The target charts need not be open immersions.
-/

noncomputable section

namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem over_pullback_snd {C : Type*} [Category C]
    {B : C} {U V X : Over B} (a : U ⟶ X) (b : V ⟶ X)
    [HasPullback a.left b.left] :
    pullback.snd a.left b.left ≫ V.hom = pullback.fst a.left b.left ≫ U.hom := by
  calc
    _ = pullback.snd a.left b.left ≫ b.left ≫ X.hom :=
      congrArg (fun k => pullback.snd a.left b.left ≫ k) b.w.symm
    _ = pullback.fst a.left b.left ≫ a.left ≫ X.hom := by
      rw [← Category.assoc, ← pullback.condition (f := a.left) (g := b.left), Category.assoc]
    _ = _ := congrArg (fun k => pullback.fst a.left b.left ≫ k) a.w

omit [IsAlgClosed K] in
private theorem points_comp_at {X Y Z : Variety K}
    {c : X.toOver ⟶ Y.toOver} {f : Y.toOver ⟶ Z.toOver}
    {d : X.toOver ⟶ Z.toOver} (h : c ≫ f = d) (p : X.points)
    {z : Z.points} (hd : Variety.mapPoints d p = z) :
    Variety.mapPoints f (Variety.mapPoints c p) = z :=
  (Variety.mapPoints_comp c f p).symm.trans
    ((congrArg (fun k => Variety.mapPoints k p) h).trans hd)

private def rootPairCover (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hcover : Set.range (c false).left ∪ Set.range (c true).left = Set.univ) :
    Scheme.OpenCover X.scheme where
  I₀ := Bool
  X _ := (additiveVariety K).scheme
  f b := (c b).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      have hx : x ∈ Set.range (c false).left ∪ Set.range (c true).left := by
        rw [hcover]
        trivial
      rcases hx with ⟨p, hp⟩ | ⟨p, hp⟩
      · exact ⟨false, p, hp⟩
      · exact ⟨true, p, hp⟩
    · infer_instance

omit [IsAlgClosed K] in
private theorem additiveReduced : IsReduced (additiveVariety K).toOver.left :=
  (additiveVariety K).reduced

omit [IsAlgClosed K] in
private theorem additiveNoetherian : IsNoetherian (additiveVariety K).toOver.left :=
  Variety.noetherian _

omit [IsAlgClosed K] in
private theorem additiveSeparated : IsSeparated (additiveVariety K).toSpec :=
  (additiveVariety K).separated

omit [IsAlgClosed K] in
private theorem additiveFiniteType : LocallyOfFiniteType (additiveVariety K).toSpec :=
  (additiveVariety K).locallyOfFiniteType

omit [IsAlgClosed K] in
private theorem additiveQuasiCompact : QuasiCompact (additiveVariety K).toSpec :=
  (additiveVariety K).quasiCompact

attribute [local instance] additiveReduced additiveNoetherian additiveSeparated
  additiveFiniteType additiveQuasiCompact

private abbrev rootPairOverlap (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) : Variety K where
  scheme := pullback (c a).left (c b).left
  toSpec := pullback.fst (c a).left (c b).left ≫ (additiveVariety K).toSpec
  reduced := isReduced_of_isOpenImmersion (pullback.fst (c a).left (c b).left)

private def rootPairFst (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) :
    (rootPairOverlap X c a b).toOver ⟶ (additiveVariety K).toOver :=
  Over.homMk (pullback.fst (c a).left (c b).left) rfl

private def rootPairSnd (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) :
    (rootPairOverlap X c a b).toOver ⟶ (additiveVariety K).toOver :=
  Over.homMk (pullback.snd (c a).left (c b).left)
    (over_pullback_snd (c a) (c b))

private theorem rootPair_compatible (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) (a b : Bool) :
    pullback.fst (c a).left (c b).left ≫ (d a).left =
      pullback.snd (c a).left (c b).left ≫ (d b).left := by
  have hc : rootPairFst X c a b ≫ c a = rootPairSnd X c a b ≫ c b := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hd : rootPairFst X c a b ≫ d a = rootPairSnd X c a b ≫ d b := by
    apply Variety.mapPoints_injective
    funext p
    simp only [Variety.mapPoints_comp]
    apply h
    simpa only [Variety.mapPoints_comp] using
      congrArg (fun f => Variety.mapPoints f p) hc
  exact congrArg Over.Hom.left hd

/-- Two compatible additive-chart maps glue on an arbitrary two-chart variety. -/
def rootCurveGluePair (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hcover : Set.range (c false).left ∪ Set.range (c true).left = Set.univ)
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) : X.toOver ⟶ Y.toOver := by
  let cov := rootPairCover X c hcover
  let f := cov.glueMorphisms (fun b => (d b).left) (rootPair_compatible X Y c d h)
  refine Over.homMk f ?_
  apply cov.hom_ext
  intro b
  change Bool at b
  have hf : (c b).left ≫ f = (d b).left :=
    cov.ι_glueMorphisms (fun b => (d b).left) (rootPair_compatible X Y c d h) b
  change (c b).left ≫ f ≫ Y.toSpec = (c b).left ≫ X.toSpec
  rw [← Category.assoc, hf]
  exact (d b).w.trans (c b).w.symm

/-- The glued morphism retains each of the two specified chart maps. -/
theorem rootCurve_glue_pair_comp (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hcover : Set.range (c false).left ∪ Set.range (c true).left = Set.univ)
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) (b : Bool) :
    c b ≫ rootCurveGluePair X Y c d hcover h = d b := by
  apply Over.OverMorphism.ext
  exact (rootPairCover X c hcover).ι_glueMorphisms
    (fun b => (d b).left) (rootPair_compatible X Y c d h) b

omit [IsAlgClosed K] in
private theorem reciprocal_compatible (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hover : ∀ t : K, Variety.mapPoints (c false) (additivePointsEquiv K t) ∈
      Set.range (Variety.mapPoints (c true)) ↔ t ≠ 0)
    (hc : ∀ t : K, t ≠ 0 →
      Variety.mapPoints (c false) (additivePointsEquiv K t) =
        Variety.mapPoints (c true) (additivePointsEquiv K t⁻¹))
    (hd : ∀ t : K, t ≠ 0 →
      Variety.mapPoints (d false) (additivePointsEquiv K t) =
        Variety.mapPoints (d true) (additivePointsEquiv K t⁻¹)) :
    ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q := by
  have cross : ∀ p q : (additiveVariety K).points,
      Variety.mapPoints (c false) p = Variety.mapPoints (c true) q →
        Variety.mapPoints (d false) p = Variety.mapPoints (d true) q := by
    intro p q he
    obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective p
    have ht : t ≠ 0 := (hover t).mp ⟨q, he.symm⟩
    have hq := Variety.mapPoints_injective_of_mono (c true) ((hc t ht).symm.trans he)
    rw [← hq]
    exact hd t ht
  intro a b p q he
  cases a <;> cases b
  · exact congrArg (Variety.mapPoints (d false))
      (Variety.mapPoints_injective_of_mono (c false) he)
  · exact cross p q he
  · exact (cross q p he.symm).symm
  · exact congrArg (Variety.mapPoints (d true))
      (Variety.mapPoints_injective_of_mono (c true) he)

private def rootLinePair (K : Type u) [Field K] (b : Bool) :
    (additiveVariety K).toOver ⟶ (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  projectiveLineChart K (if b then ⟨1⟩ else ⟨0⟩)

private instance rootLinePair_isOpen (K : Type u) [Field K] :
    ∀ b, IsOpenImmersion (rootLinePair K b).left := by
  intro b
  change IsOpenImmersion (projectiveLineChart K _).left
  infer_instance

variable [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)

private def rootTargetPair (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (b : Bool) :
    (additiveVariety K).toOver ⟶ (flagVariety G).toOver :=
  if b then rootCurveInfinityChart G w i
      (RootPairing.weylGroup.ofIdx G.rootSystem
        (G.rootSystem.weylGroupToPerm w i.val) * x)
  else rootCurveZeroChart G w i x

private theorem rootTarget_compatible (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (rootLinePair K a) p = Variety.mapPoints (rootLinePair K b) q →
        Variety.mapPoints (rootTargetPair G w i x a) p =
          Variety.mapPoints (rootTargetPair G w i x b) q :=
  reciprocal_compatible (projectiveVariety K (ULift.{u} (Fin 2))) (flagVariety G)
    (rootLinePair K) (rootTargetPair G w i x) (projectiveLineChart_overlap K)
    (fun _ ht => projectiveLineChart_transition K ht)
    (fun _ ht => rootCurve_charts_transition G w i x hpos ht)

/-- The specified projective-line root curve through the two reflected Weyl flags. -/
def rootCurveProjective (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver ⟶ (flagVariety G).toOver :=
  rootCurveGluePair (projectiveVariety K (ULift.{u} (Fin 2))) (flagVariety G)
    (rootLinePair K) (rootTargetPair G w i x) (projectiveLineChart_cover K)
    (rootTarget_compatible G w i x hpos)

/-- The first projective-line chart is the prescribed lower-root orbit at the initial flag. -/
theorem rootCurveProjective_zero (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    projectiveLineChart K ⟨0⟩ ≫ rootCurveProjective G w i x hpos =
      rootCurveZeroChart G w i x :=
  rootCurve_glue_pair_comp (projectiveVariety K (ULift.{u} (Fin 2))) (flagVariety G)
    (rootLinePair K) (rootTargetPair G w i x) (projectiveLineChart_cover K)
    (rootTarget_compatible G w i x hpos) false

/-- The second projective-line chart is the prescribed upper-root orbit at the reflected flag. -/
theorem rootCurveProjective_infinity (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    projectiveLineChart K ⟨1⟩ ≫ rootCurveProjective G w i x hpos =
      rootCurveInfinityChart G w i
        (RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm w i.val) * x) :=
  rootCurve_glue_pair_comp (projectiveVariety K (ULift.{u} (Fin 2))) (flagVariety G)
    (rootLinePair K) (rootTargetPair G w i x) (projectiveLineChart_cover K)
    (rootTarget_compatible G w i x hpos) true

/-- The origin of the first projective-line chart maps to the initial Weyl flag. -/
theorem rootCurveProjective_at_zero (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    Variety.mapPoints (rootCurveProjective G w i x hpos)
      (Variety.mapPoints (projectiveLineChart K ⟨0⟩) (additivePointsEquiv K 0)) =
        weylFlagPoint G x := by
  exact points_comp_at (rootCurveProjective_zero G w i x hpos)
    (additivePointsEquiv K 0) (rootCurve_zeroChart_zero G w i x)

/-- The origin of the second projective-line chart maps to the reflected Weyl flag. -/
theorem rootCurveProjective_at_infinity (w : G.weylGroup) (i : G.rootBase.support)
    (x : G.weylGroup) (hpos : G.rootBase.IsPos
      (G.rootSystem.weylGroupToPerm x⁻¹
        (G.rootSystem.weylGroupToPerm w i.val))) :
    Variety.mapPoints (rootCurveProjective G w i x hpos)
      (Variety.mapPoints (projectiveLineChart K ⟨1⟩) (additivePointsEquiv K 0)) =
        weylFlagPoint G (RootPairing.weylGroup.ofIdx G.rootSystem
          (G.rootSystem.weylGroupToPerm w i.val) * x) := by
  exact points_comp_at (rootCurveProjective_infinity G w i x hpos)
    (additivePointsEquiv K 0) (rootCurve_infinityChart_zero G w i _)

-- RootCurveContainment proves both scheme-image containments and the Richardson factor.

end SchubertGeometry
