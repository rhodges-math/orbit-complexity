import OrbitComplexity.SchubertGeometry.ProjectiveLine.ChartsTransition
import Mathlib.AlgebraicGeometry.Gluing
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoCharts

/-! # The simple Schubert variety is the projective line

The positive and negative simple-root charts have the same reciprocal parameter
transition as the standard charts of the polynomial projective line. Gluing their
chart morphisms in both directions gives an isomorphism over the coefficient field.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
private def pairChartCover (X : Variety K)
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
private abbrev pairOverlap (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) : Variety K where
  scheme := pullback (c a).left (c b).left
  toSpec := pullback.fst (c a).left (c b).left ≫ (additiveVariety K).toSpec
  reduced := isReduced_of_isOpenImmersion (pullback.fst (c a).left (c b).left)
private def pairOverlapFst (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) :
    (pairOverlap X c a b).toOver ⟶ (additiveVariety K).toOver :=
  Over.homMk (pullback.fst (c a).left (c b).left) rfl
private def pairOverlapSnd (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) :
    (pairOverlap X c a b).toOver ⟶ (additiveVariety K).toOver :=
  Over.homMk (pullback.snd (c a).left (c b).left) (by
    change pullback.snd (c a).left (c b).left ≫ (additiveVariety K).toSpec =
      pullback.fst (c a).left (c b).left ≫ (additiveVariety K).toSpec
    have hi : (c a).left ≫ X.toSpec = (additiveVariety K).toSpec := (c a).w
    have hj : (c b).left ≫ X.toSpec = (additiveVariety K).toSpec := (c b).w
    conv_lhs => rw [← hj]
    conv_rhs => rw [← hi]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])
omit [IsAlgClosed K] in
private theorem pairOverlap_condition (X : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    [∀ b, IsOpenImmersion (c b).left] (a b : Bool) :
    pairOverlapFst X c a b ≫ c a = pairOverlapSnd X c a b ≫ c b := by
  apply Over.OverMorphism.ext
  exact pullback.condition
private theorem pairChart_compatible (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) (a b : Bool) :
    pullback.fst (c a).left (c b).left ≫ (d a).left =
      pullback.snd (c a).left (c b).left ≫ (d b).left := by
  have he : pairOverlapFst X c a b ≫ d a = pairOverlapSnd X c a b ≫ d b := by
    apply Variety.mapPoints_injective
    funext p
    simp only [Variety.mapPoints_comp]
    apply h
    have hc := congrArg (fun f => Variety.mapPoints f p) (pairOverlap_condition X c a b)
    simpa only [Variety.mapPoints_comp] using hc
  exact congrArg Over.Hom.left he
private def pairChartHom (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hcover : Set.range (c false).left ∪ Set.range (c true).left = Set.univ)
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) : X.toOver ⟶ Y.toOver := by
  let cov := pairChartCover X c hcover
  let f := cov.glueMorphisms (fun b => (d b).left) (pairChart_compatible X Y c d h)
  refine Over.homMk f ?_
  apply cov.hom_ext
  intro b
  change Bool at b
  have hf : (c b).left ≫ f = (d b).left :=
    cov.ι_glueMorphisms (fun b => (d b).left) (pairChart_compatible X Y c d h) b
  change (c b).left ≫ f ≫ Y.toSpec = (c b).left ≫ X.toSpec
  rw [← Category.assoc, hf]
  exact (d b).w.trans (c b).w.symm
private theorem pairChartHom_comp (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left]
    (hcover : Set.range (c false).left ∪ Set.range (c true).left = Set.univ)
    (h : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q) (b : Bool) :
    c b ≫ pairChartHom X Y c d hcover h = d b := by
  apply Over.OverMorphism.ext
  exact (pairChartCover X c hcover).ι_glueMorphisms
    (fun b => (d b).left) (pairChart_compatible X Y c d h) b

omit [IsAlgClosed K] in
private theorem pairPointCompatible (X Y : Variety K)
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
private def pairChartIso (X Y : Variety K)
    (c : Bool → ((additiveVariety K).toOver ⟶ X.toOver))
    (d : Bool → ((additiveVariety K).toOver ⟶ Y.toOver))
    [∀ b, IsOpenImmersion (c b).left] [∀ b, IsOpenImmersion (d b).left]
    (hc : Set.range (c false).left ∪ Set.range (c true).left = Set.univ)
    (hd : Set.range (d false).left ∪ Set.range (d true).left = Set.univ)
    (hcd : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (c a) p = Variety.mapPoints (c b) q →
        Variety.mapPoints (d a) p = Variety.mapPoints (d b) q)
    (hdc : ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (d a) p = Variety.mapPoints (d b) q →
        Variety.mapPoints (c a) p = Variety.mapPoints (c b) q) : X.toOver ≅ Y.toOver where
  hom := pairChartHom X Y c d hc hcd
  inv := pairChartHom Y X d c hd hdc
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply (pairChartCover X c hc).hom_ext
    intro b
    change Bool at b
    have he : c b ≫ (pairChartHom X Y c d hc hcd ≫ pairChartHom Y X d c hd hdc) =
        c b ≫ 𝟙 X.toOver := by
      rw [← Category.assoc, pairChartHom_comp, pairChartHom_comp, Category.comp_id]
    exact congrArg Over.Hom.left he
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply (pairChartCover Y d hd).hom_ext
    intro b
    change Bool at b
    have he : d b ≫ (pairChartHom Y X d c hd hdc ≫ pairChartHom X Y c d hc hcd) =
        d b ≫ 𝟙 Y.toOver := by
      rw [← Category.assoc, pairChartHom_comp, pairChartHom_comp, Category.comp_id]
    exact congrArg Over.Hom.left he
variable [CharZero K] (G : ReductiveGroups.ReductiveGroupData K) (i : G.rootBase.support)
private def simplePair (b : Bool) : (additiveVariety K).toOver ⟶
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  if b then simpleNegativeChart G i else simplePositiveChart G i
private def projectivePair (b : Bool) : (additiveVariety K).toOver ⟶
    (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  projectiveLineChart K (if b then ⟨1⟩ else ⟨0⟩)
private instance simplePair_isOpen : ∀ b, IsOpenImmersion (simplePair G i b).left := by
  intro b
  cases b
  · change IsOpenImmersion (simplePositiveChart G i).left
    infer_instance
  · change IsOpenImmersion (simpleNegativeChart G i).left
    infer_instance
omit [IsAlgClosed K] [CharZero K] in
private instance projectivePair_isOpen : ∀ b, IsOpenImmersion (projectivePair (K := K) b).left :=
  fun _ => by
    change IsOpenImmersion (projectiveLineChart K _).left
    infer_instance
private theorem simplePair_cover :
    Set.range (simplePair G i false).left ∪ Set.range (simplePair G i true).left = Set.univ :=
  simpleCharts_cover G i
omit [IsAlgClosed K] [CharZero K] in
private theorem projectivePair_cover :
    Set.range (projectivePair (K := K) false).left ∪
      Set.range (projectivePair (K := K) true).left = Set.univ := projectiveLineChart_cover K
private theorem simple_projective_compatible :
    ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (simplePair G i a) p = Variety.mapPoints (simplePair G i b) q →
        Variety.mapPoints (projectivePair (K := K) a) p =
          Variety.mapPoints (projectivePair (K := K) b) q :=
  pairPointCompatible
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectiveVariety K (ULift.{u} (Fin 2))) (simplePair G i) (projectivePair (K := K))
    (simpleCharts_overlap G i)
    (fun _ ht => simpleCharts_transition G i ht)
    (fun _ ht => projectiveLineChart_transition K ht)
private theorem projective_simple_compatible :
    ∀ a b (p q : (additiveVariety K).points),
      Variety.mapPoints (projectivePair (K := K) a) p =
        Variety.mapPoints (projectivePair (K := K) b) q →
          Variety.mapPoints (simplePair G i a) p = Variety.mapPoints (simplePair G i b) q :=
  pairPointCompatible (projectiveVariety K (ULift.{u} (Fin 2)))
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectivePair (K := K)) (simplePair G i) (projectiveLineChart_overlap K)
    (fun _ ht => projectiveLineChart_transition K ht)
    (fun _ ht => simpleCharts_transition G i ht)
/-- A simple Schubert variety is the polynomial projective line over its coefficient field. -/
def simpleSchubertIso :
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ≅
      (projectiveVariety K (ULift.{u} (Fin 2))).toOver :=
  pairChartIso
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectiveVariety K (ULift.{u} (Fin 2))) (simplePair G i) (projectivePair (K := K))
    (simplePair_cover G i) (projectivePair_cover (K := K))
    (simple_projective_compatible G i) (projective_simple_compatible G i)
/-- The Schubert isomorphism identifies the positive root chart with the first standard chart. -/
theorem simpleSchubertIso_positive :
    simplePositiveChart G i ≫ (simpleSchubertIso G i).hom = projectiveLineChart K ⟨0⟩ :=
  pairChartHom_comp
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectiveVariety K (ULift.{u} (Fin 2))) (simplePair G i) (projectivePair (K := K))
    (simplePair_cover G i)
    (simple_projective_compatible G i) false
/-- The Schubert isomorphism identifies the negative root chart with the second standard chart. -/
theorem simpleSchubertIso_negative :
    simpleNegativeChart G i ≫ (simpleSchubertIso G i).hom = projectiveLineChart K ⟨1⟩ :=
  pairChartHom_comp
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (projectiveVariety K (ULift.{u} (Fin 2))) (simplePair G i) (projectivePair (K := K))
    (simplePair_cover G i)
    (simple_projective_compatible G i) true
end SchubertGeometry
