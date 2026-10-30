import OrbitComplexity.SchubertGeometry.BSDH.Paired
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntersectionOpen

/-! # Proper paired endpoints to reduced Richardson varieties

The reduced paired source factors through the Richardson inclusion.
Its comparison with a pullback of the two resolved Schubert factors retains
the endpoint, and transports properness and geometric connectedness.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u v w

section Categorical
variable {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C] [HasPullbacks C]

private def factoredIntersectionIso (D E X Y F R : C)
    (f₀ : D ⟶ F) (g₀ : E ⟶ F) (f : D ⟶ X) (g : E ⟶ Y)
    (i : X ⟶ F) (j : Y ⟶ F) (r : R ⟶ F) (rx : R ⟶ X) (ry : R ⟶ Y)
    [Mono i] [Mono j] [Mono r]
    (hf : f ≫ i = f₀) (hg : g ≫ j = g₀)
    (hrx : rx ≫ i = r) (hry : ry ≫ j = r)
    (m : pullback f₀ g₀ ⟶ R) (hm : m ≫ r = pullback.fst f₀ g₀ ≫ f₀) :
    {e : pullback f₀ g₀ ≅ pullback (f ⊗ₘ g) (lift rx ry) //
      e.hom ≫ pullback.snd (f ⊗ₘ g) (lift rx ry) = m} := by
  let P := pullback f₀ g₀
  let T := pullback (f ⊗ₘ g) (lift rx ry)
  have hx : pullback.fst f₀ g₀ ≫ f = m ≫ rx := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hf, hrx, hm]
  have hy : pullback.snd f₀ g₀ ≫ g = m ≫ ry := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, hg, hry, hm, pullback.condition]
  let h : P ⟶ T := pullback.lift
    (lift (pullback.fst f₀ g₀) (pullback.snd f₀ g₀)) m (by
      apply CartesianMonoidalCategory.hom_ext <;>
        simp only [Category.assoc, tensorHom_fst, tensorHom_snd,
          lift_fst_assoc, lift_snd_assoc, comp_lift, lift_fst, lift_snd, hx, hy])
  have tx : pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ fst D E ≫ f =
      pullback.snd (f ⊗ₘ g) (lift rx ry) ≫ rx := by
    have hc := congrArg (fun k => k ≫ fst X Y)
      (pullback.condition (f := f ⊗ₘ g) (g := lift rx ry))
    simpa only [Category.assoc, tensorHom_fst, lift_fst] using hc
  have ty : pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ snd D E ≫ g =
      pullback.snd (f ⊗ₘ g) (lift rx ry) ≫ ry := by
    have hc := congrArg (fun k => k ≫ snd X Y)
      (pullback.condition (f := f ⊗ₘ g) (g := lift rx ry))
    simpa only [Category.assoc, tensorHom_snd, lift_snd] using hc
  let k : T ⟶ P := pullback.lift
    (pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ fst D E)
    (pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ snd D E) (by
      calc
        _ = (pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ fst D E ≫ f) ≫ i := by
          simp only [Category.assoc, hf]
        _ = (pullback.snd (f ⊗ₘ g) (lift rx ry) ≫ rx) ≫ i :=
          congrArg (fun m => m ≫ i) tx
        _ = pullback.snd (f ⊗ₘ g) (lift rx ry) ≫ r := by rw [Category.assoc, hrx]
        _ = (pullback.snd (f ⊗ₘ g) (lift rx ry) ≫ ry) ≫ j := by rw [Category.assoc, hry]
        _ = (pullback.fst (f ⊗ₘ g) (lift rx ry) ≫ snd D E ≫ g) ≫ j :=
          congrArg (fun m => m ≫ j) ty.symm
        _ = _ := by simp only [Category.assoc, hg])
  refine ⟨{ hom := h, inv := k, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_⟩
  · apply pullback.hom_ext <;> simp [h, k]
  · apply pullback.hom_ext
    · apply CartesianMonoidalCategory.hom_ext <;> simp [h, k]
    · apply (cancel_mono r).mp
      simp only [Category.assoc, h, pullback.lift_snd_assoc, Category.id_comp]
      rw [hm]
      simp only [k, pullback.lift_fst_assoc]
      rw [← hf]
      simpa only [Category.assoc, hrx] using congrArg (fun m => m ≫ i) tx
  · simp [h]

end Categorical

private def factorOver {S : Scheme.{u}} {X Y Z : Over S} (i : Z ⟶ X) (f : Y ⟶ X)
    [IsPreimmersion i.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) : Y ⟶ Z :=
  Over.homMk (liftPreimmersion i.left f.left h) (by
    rw [← i.w, ← Category.assoc, liftPreimmersion_fac]
    exact f.w)

private theorem factorOver_comp {S : Scheme.{u}} {X Y Z : Over S}
    (i : Z ⟶ X) (f : Y ⟶ X) [IsPreimmersion i.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) : factorOver i f h ≫ i = f := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac _ _ h

private theorem properGC_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [GeometricallyConnected f] [GeometricallyConnected g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ z
  have : ConnectedSpace (pullback g z : Scheme.{u}) :=
    pullback_of_geometrically
      (inferInstance : GeometricallyConnected g).geometrically_connectedSpace L z
  rw [← (pullbackRightPullbackFstIso g z f).hom.homeomorph.connectedSpace_iff]
  exact FrobeniusSplitting.connectedSpace_of_proper (pullback.snd f (pullback.fst g z))

private abbrev properConnected : MorphismProperty Scheme.{u} :=
  @IsProper ⊓ @GeometricallyConnected

private theorem properConnected_baseChange :
    MorphismProperty.IsStableUnderBaseChange (properConnected.{u}) where
  of_isPullback h hh :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) h hh.1,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hh.2⟩

private theorem properConnected_compStable :
    MorphismProperty.IsStableUnderComposition (properConnected.{u}) where
  comp_mem f g hf hg := by
    have : IsProper f := hf.1
    have : IsProper g := hg.1
    have : GeometricallyConnected f := hf.2
    have : GeometricallyConnected g := hg.2
    exact ⟨inferInstance, properGC_comp f g⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private abbrev ordinaryEndpoint (a : List G.rootBase.support) :
    (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (bsdhMap G a) rfl

private theorem ordinaryFactor_comp (a : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a) :
    bsdhSchubertMap G a ha ≫
        schubertInclusion G (ReductiveGroups.simpleWeylWord G.rootBase a) =
      ordinaryEndpoint G a := by
  apply Over.OverMorphism.ext
  exact bsdhSchubertMap_comp G a ha

private theorem pairedEndpoint_range (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    Set.range (pullback.fst (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b) ≫
        ordinaryEndpoint G a).left ⊆
      Set.range (richardsonInclusion G
        (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
        (ReductiveGroups.simpleWeylWord G.rootBase a)).left := by
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  rw [richardsonInclusion_range]
  constructor
  · refine ⟨(bsdhSchubertMap G a ha).left
      ((pullback.fst (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b)).left p), ?_⟩
    exact congrArg (fun f => f.left
      ((pullback.fst (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b)).left p))
        (ordinaryFactor_comp G a ha)
  · refine ⟨(bsdhOppositeSchubertMap G b hb).left
      ((pullback.snd (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b)).left p), ?_⟩
    have hs := congrArg (fun f => f.left
      ((pullback.snd (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b)).left p))
        (bsdhOppositeSchubertMap_comp G b hb)
    have hp := congrArg (fun f : pairedBSDHSource G a b ⟶ (flagVariety G).toOver => f.left p)
      (pullback.condition (f := ordinaryEndpoint G a) (g := bsdhOppositeEndpoint G b))
    exact hs.trans hp.symm

/-- The paired endpoint factors through the reduced Richardson variety. -/
def pairedRichardsonMap (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    pairedBSDHSource G a b ⟶ (richardsonVariety G
      (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
      (ReductiveGroups.simpleWeylWord G.rootBase a)).toOver :=
  factorOver (richardsonInclusion G
      (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
      (ReductiveGroups.simpleWeylWord G.rootBase a))
    (pullback.fst (ordinaryEndpoint G a) (bsdhOppositeEndpoint G b) ≫
      ordinaryEndpoint G a) (pairedEndpoint_range G a b ha hb)

/-- The Richardson factor recovers the paired flag endpoint. -/
theorem pairedRichardsonMap_comp (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    pairedRichardsonMap G a b ha hb ≫ richardsonInclusion G
        (G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b)
        (ReductiveGroups.simpleWeylWord G.rootBase a) =
      pullback.fst (Over.homMk (bsdhMap G a) rfl :
        (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b) ≫
        (Over.homMk (bsdhMap G a) rfl :
          (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) :=
  factorOver_comp _ _ (pairedEndpoint_range G a b ha hb)

private theorem pairedRichardson_properties (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    IsProper (pairedRichardsonMap G a b ha hb).left ∧
      GeometricallyConnected (pairedRichardsonMap G a b ha hb).left := by
  let v := ReductiveGroups.simpleWeylWord G.rootBase a
  let u := G.longestElement * ReductiveGroups.simpleWeylWord G.rootBase b
  let f := bsdhSchubertMap G a ha
  let g := bsdhOppositeSchubertMap G b hb
  let rx := richardsonToSchubert G u v
  let ry := richardsonToOpposite G u v
  have : Mono (schubertInclusion G v) := Over.mono_of_mono_left _
  have : Mono (oppositeSchubertInclusion G u) := Over.mono_of_mono_left _
  have : Mono (richardsonInclusion G u v) := Over.mono_of_mono_left _
  let e := factoredIntersectionIso _ _ _ _ _ _ (ordinaryEndpoint G a)
    (bsdhOppositeEndpoint G b) f g (schubertInclusion G v)
    (oppositeSchubertInclusion G u) (richardsonInclusion G u v) rx ry
    (ordinaryFactor_comp G a ha) (bsdhOppositeSchubertMap_comp G b hb)
    (richardsonToSchubert_comp G u v) (richardsonToOpposite_comp G u v)
    (pairedRichardsonMap G a b ha hb) (pairedRichardsonMap_comp G a b ha hb)
  have hc : IsPullback (pullback.fst (f ⊗ₘ g) (lift rx ry)).left
      (pullback.snd (f ⊗ₘ g) (lift rx ry)).left (f ⊗ₘ g).left (lift rx ry).left :=
    (IsPullback.of_hasPullback (f ⊗ₘ g) (lift rx ry)).map
      (Over.forget (Spec (CommRingCat.of K)))
  have : GeometricallyConnected f.left := bsdhSchubert_geomConnected G a ha
  have : GeometricallyConnected g.left := bsdhOppositeSchubert_geomConnected G b hb
  let := properConnected_compStable.{u}
  let := properConnected_baseChange.{u}
  have hproduct : properConnected (f ⊗ₘ g).left :=
    MorphismProperty.pullbackMap (P := properConnected)
      ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩ f.w.symm g.w.symm
  have hp : IsProper (pullback.snd (f ⊗ₘ g) (lift rx ry)).left :=
    MorphismProperty.of_isPullback hc hproduct.1
  have hg : GeometricallyConnected (pullback.snd (f ⊗ₘ g) (lift rx ry)).left :=
    MorphismProperty.of_isPullback hc hproduct.2
  have he : e.val.hom.left ≫ (pullback.snd (f ⊗ₘ g) (lift rx ry)).left =
      (pairedRichardsonMap G a b ha hb).left := congrArg Over.Hom.left e.property
  have : IsIso e.val.hom.left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map e.val.hom)
    infer_instance
  constructor
  · rw [← he]
    infer_instance
  · rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      e.val.hom.left (pullback.snd (f ⊗ₘ g) (lift rx ry)).left).mpr hg

/-- The paired Richardson endpoint is proper. -/
instance pairedRichardsonMap_isProper (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    IsProper (pairedRichardsonMap G a b ha hb).left :=
  (pairedRichardson_properties G a b ha hb).1

/-- The paired Richardson endpoint has geometrically connected fibres. -/
theorem pairedRichardsonMap_geomConnected (a b : List G.rootBase.support)
    (ha : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (ReductiveGroups.weylCoxeterSystem G.rootBase).IsReduced b) :
    GeometricallyConnected (pairedRichardsonMap G a b ha hb).left :=
  (pairedRichardson_properties G a b ha hb).2

end
end SchubertGeometry
