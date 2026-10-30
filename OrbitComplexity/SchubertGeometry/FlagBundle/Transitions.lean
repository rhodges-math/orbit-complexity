import OrbitComplexity.SchubertGeometry.FlagVariety.TorsorTransitions
import OrbitComplexity.GroupActions.Actions.RelativeTwist

/-! # Fibre coordinates over flag charts

The Borel factors of flag chart changes act on varieties with a Borel action. The resulting
product transitions satisfy the cocycle identity, and triple overlaps commute with products.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K]

private def fibreMap {H A B Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (b : A ⟶ H) : A ⊗ Y ⟶ B ⊗ Y :=
  lift (fst A Y ≫ f) ((fst A Y ≫ b) • snd A Y)

private theorem fibreMap_fst {H A B Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (b : A ⟶ H) :
    fibreMap (Y := Y) f b ≫ fst B Y = fst A Y ≫ f := by
  simp [fibreMap]

private theorem fibreMap_snd {H A B Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (b : A ⟶ H) :
    fibreMap (Y := Y) f b ≫ snd B Y = (fst A Y ≫ b) • snd A Y := by
  simp [fibreMap]

private theorem fibreMap_comp {H A B C Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (g : B ⟶ C)
    (b : A ⟶ H) (c : B ⟶ H) :
    fibreMap (Y := Y) f b ≫ fibreMap g c = fibreMap (f ≫ g) ((f ≫ c) * b) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [fibreMap, Category.assoc]
  · simp [fibreMap, ModObj.comp_smul, MonObj.comp_mul, Category.assoc, mul_smul]

private theorem fibreMap_one {H A Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] : fibreMap (Y := Y) (𝟙 A) (1 : A ⟶ H) = 𝟙 (A ⊗ Y) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [fibreMap]

private theorem fibreMap_right_tensor {H A B C Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (g : B ⟶ C) (b : A ⟶ H) :
    fibreMap (Y := Y) f b ≫ (g ⊗ₘ 𝟙 Y) = fibreMap (f ≫ g) b := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [fibreMap, Category.assoc]

private theorem fibreMap_left_tensor {H A B C Y : Over (Spec (CommRingCat.of K))}
    [GrpObj H] [ModObj H Y] (f : A ⟶ B) (g : B ⟶ C) (b : B ⟶ H) :
    (f ⊗ₘ 𝟙 Y) ≫ fibreMap (Y := Y) g b = fibreMap (f ≫ g) (f ≫ b) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [fibreMap, ModObj.comp_smul]

private def pullbackTensorIso {A B D : Over (Spec (CommRingCat.of K))}
    (f : A ⟶ D) (g : B ⟶ D) (Y : Over (Spec (CommRingCat.of K))) :
    pullback f g ⊗ Y ≅ pullback (f ⊗ₘ 𝟙 Y) (g ⊗ₘ 𝟙 Y) where
  hom := pullback.lift
    (lift (fst (pullback f g) Y ≫ pullback.fst f g) (snd (pullback f g) Y))
    (lift (fst (pullback f g) Y ≫ pullback.snd f g) (snd (pullback f g) Y)) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc]
        exact congrArg (fun m => fst (pullback f g) Y ≫ m) (pullback.condition (f := f))
      · simp)
  inv := lift
    (pullback.lift
      (pullback.fst (f ⊗ₘ 𝟙 Y) (g ⊗ₘ 𝟙 Y) ≫ fst A Y)
      (pullback.snd (f ⊗ₘ 𝟙 Y) (g ⊗ₘ 𝟙 Y) ≫ fst B Y) (by
        have he := congrArg (fun m => m ≫ fst D Y)
          (pullback.condition (f := f ⊗ₘ 𝟙 Y) (g := g ⊗ₘ 𝟙 Y))
        simpa only [Category.assoc, tensorHom_fst] using he))
    (pullback.fst (f ⊗ₘ 𝟙 Y) (g ⊗ₘ 𝟙 Y) ≫ snd A Y)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply pullback.hom_ext <;> simp
    · simp
  inv_hom_id := by
    have hs := congrArg (fun m => m ≫ snd D Y)
      (pullback.condition (f := f ⊗ₘ 𝟙 Y) (g := g ⊗ₘ 𝟙 Y))
    simp only [Category.assoc, tensorHom_snd, Category.comp_id] at hs
    apply pullback.hom_ext
    · apply CartesianMonoidalCategory.hom_ext <;> simp
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using hs

private theorem pullbackTensorIso_hom_fst {A B D : Over (Spec (CommRingCat.of K))}
    (f : A ⟶ D) (g : B ⟶ D) (Y : Over (Spec (CommRingCat.of K))) :
    (pullbackTensorIso f g Y).hom ≫ pullback.fst _ _ = pullback.fst f g ⊗ₘ 𝟙 Y := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pullbackTensorIso]

private theorem pullbackTensorIso_hom_snd {A B D : Over (Spec (CommRingCat.of K))}
    (f : A ⟶ D) (g : B ⟶ D) (Y : Over (Spec (CommRingCat.of K))) :
    (pullbackTensorIso f g Y).hom ≫ pullback.snd _ _ = pullback.snd f g ⊗ₘ 𝟙 Y := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pullbackTensorIso]

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroups.ReductiveGroupData K)

private theorem borel_self (g : G.points) : flagOverlapBorel G g g = 1 := by
  have hc : flagOverlapCoordinate G g g = flagOverlapInclusion G g g := by
    rw [← flagTransition_comp, flagTransition_self, Category.id_comp]
  have he := flagTorsor_section G g g
  rw [hc] at he
  have hb : flagOverlapBorel G g g ≫ GroupActions.borelInclusion G = 1 := by
    apply mul_left_cancel (a := flagOverlapInclusion G g g ≫ flagChartMap G g)
    simpa only [mul_one] using he.symm
  have : Mono (GroupActions.borelInclusion G) :=
    Over.mono_of_mono_left (GroupActions.borelInclusion G)
  apply (cancel_mono (GroupActions.borelInclusion G)).mp
  simpa only [MonObj.one_comp] using hb

variable (Y : GroupActions.Variety K)

/-- The inclusion of a chart overlap, with unchanged fibre coordinate. -/
abbrev flagBundleInclusion (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⊗ Y.toOver ⟶
      (GroupActions.oppositeUnipotentVariety G).toOver ⊗ Y.toOver :=
  flagOverlapInclusion G g h ⊗ₘ 𝟙 Y.toOver

private theorem triple_pullback (g h k : G.points) :
    IsPullback (flagTripleFst G g h k) (flagTripleSnd G g h k)
      (flagOverlapInclusion G g h) (flagOverlapInclusion G g k) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of K)))
  exact IsPullback.of_hasPullback _ _

private def tripleOverIso (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⊗ Y.toOver ≅
      pullback (flagBundleInclusion G Y g h) (flagBundleInclusion G Y g k) :=
  tensorIso (triple_pullback G g h k).isoPullback (Iso.refl Y.toOver) ≪≫
    pullbackTensorIso (flagOverlapInclusion G g h) (flagOverlapInclusion G g k) Y.toOver

private theorem tripleOverIso_fst (g h k : G.points) :
    (tripleOverIso G Y g h k).hom ≫ pullback.fst _ _ = flagTripleFst G g h k ⊗ₘ 𝟙 Y.toOver := by
  dsimp only [tripleOverIso, Iso.trans_hom]
  rw [Category.assoc, pullbackTensorIso_hom_fst]
  change ((triple_pullback G g h k).isoPullback.hom ⊗ₘ 𝟙 Y.toOver) ≫
    (pullback.fst _ _ ⊗ₘ 𝟙 Y.toOver) = _
  rw [tensorHom_comp_tensorHom, Category.comp_id, IsPullback.isoPullback_hom_fst]

private theorem tripleOverIso_snd (g h k : G.points) :
    (tripleOverIso G Y g h k).hom ≫ pullback.snd _ _ = flagTripleSnd G g h k ⊗ₘ 𝟙 Y.toOver := by
  dsimp only [tripleOverIso, Iso.trans_hom]
  rw [Category.assoc, pullbackTensorIso_hom_snd]
  change ((triple_pullback G g h k).isoPullback.hom ⊗ₘ 𝟙 Y.toOver) ≫
    (pullback.snd _ _ ⊗ₘ 𝟙 Y.toOver) = _
  rw [tensorHom_comp_tensorHom, Category.comp_id, IsPullback.isoPullback_hom_snd]

/-- The product of a triple chart overlap is the overlap of product charts. -/
def flagBundleTripleIso (g h k : G.points) :
    ((flagTripleVariety G g h k).toOver ⊗ Y.toOver).left ≅
      pullback (flagBundleInclusion G Y g h).left (flagBundleInclusion G Y g k).left :=
  (Over.forget (Spec (CommRingCat.of K))).mapIso (tripleOverIso G Y g h k) ≪≫
    PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K)))
      (flagBundleInclusion G Y g h) (flagBundleInclusion G Y g k)

/-- The overlap-product isomorphism preserves its first projection. -/
theorem flagBundleTripleIso_fst (g h k : G.points) :
    (flagBundleTripleIso G Y g h k).hom ≫ pullback.fst _ _ =
      (flagTripleFst G g h k ⊗ₘ 𝟙 Y.toOver).left := by
  have hp := PreservesPullback.iso_hom_fst (Over.forget (Spec (CommRingCat.of K)))
    (flagBundleInclusion G Y g h) (flagBundleInclusion G Y g k)
  simp only [Over.forget_map] at hp
  dsimp only [flagBundleTripleIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, hp]
  exact congrArg Over.Hom.left (tripleOverIso_fst G Y g h k)

/-- The overlap-product isomorphism preserves its second projection. -/
theorem flagBundleTripleIso_snd (g h k : G.points) :
    (flagBundleTripleIso G Y g h k).hom ≫ pullback.snd _ _ =
      (flagTripleSnd G g h k ⊗ₘ 𝟙 Y.toOver).left := by
  have hp := PreservesPullback.iso_hom_snd (Over.forget (Spec (CommRingCat.of K)))
    (flagBundleInclusion G Y g h) (flagBundleInclusion G Y g k)
  simp only [Over.forget_map] at hp
  dsimp only [flagBundleTripleIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, hp]
  exact congrArg Over.Hom.left (tripleOverIso_snd G Y g h k)

variable [ModObj (GroupActions.borelVariety G).toOver Y.toOver]

/-- The Borel change of chart acts on the fibre of an associated bundle. -/
def flagBundleTransition (g h : G.points) :
    (flagOverlapVariety G g h).toOver ⊗ Y.toOver ⟶
      (flagOverlapVariety G h g).toOver ⊗ Y.toOver :=
  fibreMap (flagTransition G g h) (flagOverlapBorel G g h)

/-- Changing charts changes the base by the flag transition. -/
theorem flagBundleTransition_fst (g h : G.points) :
    flagBundleTransition G Y g h ≫ fst (flagOverlapVariety G h g).toOver Y.toOver =
      fst (flagOverlapVariety G g h).toOver Y.toOver ≫ flagTransition G g h :=
  fibreMap_fst _ _

/-- Changing charts acts on the fibre by its Borel factor. -/
theorem flagBundleTransition_snd (g h : G.points) :
    flagBundleTransition G Y g h ≫ snd (flagOverlapVariety G h g).toOver Y.toOver =
      (fst (flagOverlapVariety G g h).toOver Y.toOver ≫ flagOverlapBorel G g h) •
        snd (flagOverlapVariety G g h).toOver Y.toOver :=
  fibreMap_snd _ _

/-- The change from a chart to itself is the identity. -/
theorem flagBundleTransition_self (g : G.points) :
    flagBundleTransition G Y g g = 𝟙 _ := by
  unfold flagBundleTransition
  rw [flagTransition_self, borel_self]
  exact fibreMap_one

private def tripleSection (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  flagTripleFst G g h k ≫ flagOverlapInclusion G g h ≫ flagChartMap G g

private def tripleBorel (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (GroupActions.borelVariety G).toOver :=
  flagTripleFst G g h k ≫ flagOverlapBorel G g h

private theorem triple_section (g h k : G.points) :
    tripleSection G g h k =
      (flagTripleTransition G g h k ≫ tripleSection G h k g) *
        (tripleBorel G g h k ≫ GroupActions.borelInclusion G) := by
  have hc : flagTripleTransition G g h k ≫ flagTripleFst G h k g ≫
        flagOverlapInclusion G h k =
      flagTripleFst G g h k ≫ flagOverlapCoordinate G g h := by
    rw [← Category.assoc, flagTripleTransition_fst, flagTripleCoordinate_comp,
      flagTransition_comp]
  have hs : flagTripleTransition G g h k ≫ tripleSection G h k g =
      flagTripleFst G g h k ≫ flagOverlapCoordinate G g h ≫ flagChartMap G h := by
    simpa only [tripleSection, Category.assoc] using
      congrArg (fun f => f ≫ flagChartMap G h) hc
  have he := congrArg (fun f => flagTripleFst G g h k ≫ f) (flagTorsor_section G g h)
  rw [hs]
  simpa only [tripleSection, tripleBorel, Category.assoc, MonObj.comp_mul] using he

private theorem triple_borel_cycle (g h k : G.points) :
    ((flagTripleTransition G g h k ≫ flagTripleTransition G h k g) ≫
        tripleBorel G k g h) *
      ((flagTripleTransition G g h k ≫ tripleBorel G h k g) * tripleBorel G g h k) = 1 := by
  have h0 := triple_section G g h k
  have h1 := congrArg (fun f => flagTripleTransition G g h k ≫ f)
    (triple_section G h k g)
  have h2 := congrArg (fun f =>
    (flagTripleTransition G g h k ≫ flagTripleTransition G h k g) ≫ f)
    (triple_section G k g h)
  simp only [MonObj.comp_mul, Category.assoc] at h1 h2
  have hs : flagTripleTransition G g h k ≫ flagTripleTransition G h k g ≫
      flagTripleTransition G k g h ≫ tripleSection G g h k = tripleSection G g h k := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun f => f ≫ tripleSection G g h k) (flagTripleTransition_cycle G g h k)
  rw [hs] at h2
  have hb : (((flagTripleTransition G g h k ≫ flagTripleTransition G h k g) ≫
        tripleBorel G k g h) *
      ((flagTripleTransition G g h k ≫ tripleBorel G h k g) * tripleBorel G g h k)) ≫
        GroupActions.borelInclusion G = 1 := by
    apply mul_left_cancel (a := tripleSection G g h k)
    simp only [MonObj.mul_comp, Category.assoc]
    rw [← mul_assoc, ← mul_assoc, ← h2, ← h1, ← h0, mul_one]
  have : Mono (GroupActions.borelInclusion G) :=
    Over.mono_of_mono_left (GroupActions.borelInclusion G)
  apply (cancel_mono (GroupActions.borelInclusion G)).mp
  simpa only [MonObj.one_comp] using hb

/-- The cyclic change of three product charts acts on their fibre. -/
def flagBundleTripleTransition (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⊗ Y.toOver ⟶
      (flagTripleVariety G h k g).toOver ⊗ Y.toOver :=
  fibreMap (flagTripleTransition G g h k) (tripleBorel G g h k)

/-- Cyclic chart changes restrict to the pairwise fibre transition. -/
theorem flagBundleTripleTransition_snd (g h k : G.points) :
    flagBundleTripleTransition G Y g h k ≫ (flagTripleSnd G h k g ⊗ₘ 𝟙 Y.toOver) =
      (flagTripleFst G g h k ⊗ₘ 𝟙 Y.toOver) ≫ flagBundleTransition G Y g h := by
  unfold flagBundleTripleTransition flagBundleTransition
  rw [fibreMap_right_tensor, fibreMap_left_tensor, flagTripleTransition_snd]
  rfl

/-- Three cyclic product-chart changes compose to the identity. -/
theorem flagBundleTripleTransition_cycle (g h k : G.points) :
    flagBundleTripleTransition G Y g h k ≫ flagBundleTripleTransition G Y h k g ≫
      flagBundleTripleTransition G Y k g h = 𝟙 _ := by
  unfold flagBundleTripleTransition
  rw [← Category.assoc, fibreMap_comp, fibreMap_comp, Category.assoc,
    flagTripleTransition_cycle, triple_borel_cycle]
  exact fibreMap_one

end SchubertGeometry
