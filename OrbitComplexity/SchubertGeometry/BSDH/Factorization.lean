import OrbitComplexity.SchubertGeometry.BSDH.FactorizationStep
import OrbitComplexity.SchubertGeometry.BSDH.Variety

/-! # Reduced-word Schubert endpoint morphisms

For a reduced word, successive ascending simple correspondences remain in the Schubert
variety of the word product. The iterated endpoint therefore factors as a proper morphism
to that Schubert variety over the coefficient field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem baseFlag_mem : baseFlagPoint G ∈
    Set.range (Variety.mapPoints (schubertInclusion G 1)) := by
  have hw : weylFlagPoint G 1 = baseFlagPoint G := by
    unfold weylFlagPoint baseFlagPoint baseFlag
    rw [G.weylPoint_eq, weylElementPoint_one]
  rw [← hw]
  exact (weylFlag_mem_schubert_iff G 1 1).mpr (WeylBruhatLE.refl _ _)

set_option maxHeartbeats 400000 in
/-- The endpoint for a reduced word lies in the Schubert variety of its product. -/
theorem bsdhMap_range_subset (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    Set.range (bsdhMap G word) ⊆
      Set.range (schubertInclusion G (simpleWeylWord G.rootBase word)).left := by
  induction word using List.reverseRecOn with
  | nil =>
    rintro _ ⟨z, rfl⟩
    change (baseFlagPoint G).val z ∈ Set.range (schubertInclusion G 1).left
    obtain ⟨x, hx⟩ := baseFlag_mem G
    refine ⟨x.val z, ?_⟩
    exact congrArg (fun f => f z) (congrArg Subtype.val hx)
  | append_singleton word i ih =>
    rintro _ ⟨z, rfl⟩
    have hprefix : (weylCoxeterSystem G.rootBase).IsReduced word := by
      simpa using hred.take word.length
    have hnum := (weylCoxeterSystem_isReduced_iff G.rootBase (word ++ [i])).mp hred
    have hi := isPos_of_reduced_append G.rootBase word i hnum
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    let π := flagBundleProjection G Y
    let P := pullback (bsdhMap G word) π
    let p : P := (bsdhAppendIso G word i).hom.left z
    have hpb := congrArg (fun f => f p)
      (pullback.condition (f := bsdhMap G word) (g := π))
    change bsdhMap G word ((pullback.fst (bsdhMap G word) π) p) =
      π ((pullback.snd (bsdhMap G word) π) p) at hpb
    have hmem : π ((pullback.snd (bsdhMap G word) π) p) ∈
        Set.range (schubertInclusion G (simpleWeylWord G.rootBase word)).left := by
      rw [← hpb]
      exact ih hprefix ⟨_, rfl⟩
    have hs := schubertAscentStep_mem G (simpleWeylWord G.rootBase word) i hi
      ((pullback.snd (bsdhMap G word) π) p) hmem
    have he := congrArg (fun f => f z) (bsdhAppendIso_endpoint G word i)
    change flagBundleMap G Y
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
        ((pullback.snd (bsdhMap G word) π) p) = bsdhMap G (word ++ [i]) z at he
    rw [← he]
    rw [simpleWeylWord_append_singleton]
    exact hs

/-- The reduced-word endpoint factors through its Schubert variety over the base field. -/
def bsdhSchubertMap (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    (bsdhVariety G word).toOver ⟶
      (schubertVariety G (simpleWeylWord G.rootBase word)).toOver :=
  Over.homMk
    (liftPreimmersion (X := (flagVariety G).scheme) (Y := bsdhScheme G word)
      (Z := (schubertVariety G (simpleWeylWord G.rootBase word)).scheme)
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left
      (bsdhMap G word) (bsdhMap_range_subset G word hred)) (by
    rw [← (schubertInclusion G (simpleWeylWord G.rootBase word)).w,
      ← Category.assoc, liftPreimmersion_fac]
    rfl)

/-- The Schubert endpoint factorization recovers the endpoint in the flag variety. -/
theorem bsdhSchubertMap_comp (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    (bsdhSchubertMap G word hred).left ≫
        (schubertInclusion G (simpleWeylWord G.rootBase word)).left = bsdhMap G word :=
  liftPreimmersion_fac (X := (flagVariety G).scheme) (Y := bsdhScheme G word)
    (Z := (schubertVariety G (simpleWeylWord G.rootBase word)).scheme)
    (schubertInclusion G (simpleWeylWord G.rootBase word)).left
    (bsdhMap G word) (bsdhMap_range_subset G word hred)

/-- The reduced-word endpoint morphism to its Schubert variety is proper. -/
instance bsdhSchubertMap_isProper (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    IsProper (bsdhSchubertMap G word hred).left := by
  have : IsProper ((bsdhSchubertMap G word hred).left ≫
      (schubertInclusion G (simpleWeylWord G.rootBase word)).left) := by
    rw [bsdhSchubertMap_comp]
    infer_instance
  exact IsProper.of_comp _ (schubertInclusion G (simpleWeylWord G.rootBase word)).left

end SchubertGeometry
