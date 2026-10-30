import OrbitComplexity.SchubertGeometry.Parabolics.SimpleIncidence
import OrbitComplexity.SchubertGeometry.BSDH.Variety
import OrbitComplexity.SchubertGeometry.FlagVariety.BorelStabilizer
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.SchubertGeometry.Parabolics.Schubert
import OrbitComplexity.GroupActions.Actions.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Borel actions on iterated simple correspondences

The incidence pullback action gives a Borel action on each iterated correspondence.
Its endpoint morphism is equivariant.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u v

private instance refl_isMonHom {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (H : C) [MonObj H] : IsMonHom (Iso.refl H).hom := by
  change IsMonHom (𝟙 H)
  infer_instance

private theorem transport_inverse {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (H : C) [MonObj H] {X Y : C}
    [ModObj H X] (e : X ≅ Y) :
    let := ModObj.ofIso (Iso.refl H) e
    IsModHom H e.inv := by
  let := ModObj.ofIso (Iso.refl H) e
  constructor
  change ((𝟙 H ⊗ₘ e.inv) ≫ γ[H, X] ≫ e.hom) ≫ e.inv =
    (H ◁ e.inv) ≫ γ[H, X]
  simp

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)

private abbrev simpleFibre : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private abbrev simpleBundle : Over (Spec (CommRingCat.of K)) :=
  Over.mk (flagBundleProjection G (simpleFibre G i) ≫ (flagVariety G).toSpec)

private theorem partial_borel : IsModHom (borelVariety G).toOver
    (partialFlagMorphism G {i}) := by
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G {i}) :=
    partialFlagMorphism_isModHom G {i}
  exact Mod.scalarRestriction_hom (borelInclusion G) _ _ (partialFlagMorphism G {i})

private def incidenceOverIso : simpleBundle G i ≅
    pullback (partialFlagMorphism G {i}) (partialFlagMorphism G {i}) := by
  let p := partialFlagMorphism G {i}
  let e := Classical.choose (simpleSchubert_incidence G i)
  let c := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) p p
  refine Over.isoMk (e ≪≫ c.symm) ?_
  change (e.hom ≫ c.inv) ≫ (pullback p p).hom = _
  rw [← (pullback.fst p p).w, ← Category.assoc, Category.assoc]
  change e.hom ≫ (c.inv ≫ (pullback.fst p p).left) ≫ _ = _
  have hcf := PreservesPullback.iso_inv_fst
    (Over.forget (Spec (CommRingCat.of K))) p p
  change c.inv ≫ (pullback.fst p p).left = pullback.fst p.left p.left at hcf
  rw [hcf]
  rw [← Category.assoc, (Classical.choose_spec (simpleSchubert_incidence G i)).1]
  rfl

@[instance_reducible] private def incidenceAction : ModObj (borelVariety G).toOver
    (pullback (partialFlagMorphism G {i}) (partialFlagMorphism G {i})) := by
  letI := partial_borel G i
  exact pullbackAction (borelVariety G).toOver _ _

@[instance_reducible] private def simpleBundleAction :
    ModObj (borelVariety G).toOver (simpleBundle G i) := by
  letI := incidenceAction G i
  exact ModObj.ofIso (Iso.refl (borelVariety G).toOver) (incidenceOverIso G i).symm

private theorem incidenceOverIso_equivariant :
    letI := simpleBundleAction G i
    letI := incidenceAction G i
    IsModHom (borelVariety G).toOver (incidenceOverIso G i).hom := by
  let := incidenceAction G i
  exact transport_inverse (borelVariety G).toOver (incidenceOverIso G i).symm

private def simpleProjectionOver : simpleBundle G i ⟶ (flagVariety G).toOver :=
  Over.homMk (flagBundleProjection G (simpleFibre G i)) rfl

private def simpleEndpointOver : simpleBundle G i ⟶ (flagVariety G).toOver :=
  Over.homMk (flagBundleMap G (simpleFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))
    (flagBundleMap_toSpec G (simpleFibre G i)
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))

private theorem incidenceOverIso_fst : (incidenceOverIso G i).hom ≫
    pullback.fst (partialFlagMorphism G {i}) (partialFlagMorphism G {i}) =
      simpleProjectionOver G i := by
  apply (Over.forget (Spec (CommRingCat.of K))).map_injective
  let p := partialFlagMorphism G {i}
  let e := Classical.choose (simpleSchubert_incidence G i)
  let c := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) p p
  change (e.hom ≫ c.inv) ≫ (pullback.fst p p).left = _
  have hcf := PreservesPullback.iso_inv_fst
    (Over.forget (Spec (CommRingCat.of K))) p p
  change c.inv ≫ (pullback.fst p p).left = pullback.fst p.left p.left at hcf
  rw [Category.assoc, hcf]
  exact (Classical.choose_spec (simpleSchubert_incidence G i)).1

private theorem incidenceOverIso_snd : (incidenceOverIso G i).hom ≫
    pullback.snd (partialFlagMorphism G {i}) (partialFlagMorphism G {i}) =
      simpleEndpointOver G i := by
  apply (Over.forget (Spec (CommRingCat.of K))).map_injective
  let p := partialFlagMorphism G {i}
  let e := Classical.choose (simpleSchubert_incidence G i)
  let c := PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K))) p p
  change (e.hom ≫ c.inv) ≫ (pullback.snd p p).left = _
  have hcs := PreservesPullback.iso_inv_snd
    (Over.forget (Spec (CommRingCat.of K))) p p
  change c.inv ≫ (pullback.snd p p).left = pullback.snd p.left p.left at hcs
  rw [Category.assoc, hcs]
  exact (Classical.choose_spec (simpleSchubert_incidence G i)).2

private theorem simpleProjection_equivariant :
    letI := simpleBundleAction G i
    IsModHom (borelVariety G).toOver (simpleProjectionOver G i) := by
  let := simpleBundleAction G i
  let := incidenceAction G i
  let : IsModHom (borelVariety G).toOver (incidenceOverIso G i).hom :=
    incidenceOverIso_equivariant G i
  let : IsModHom (borelVariety G).toOver
      (pullback.fst (partialFlagMorphism G {i}) (partialFlagMorphism G {i})) := by
    let := partial_borel G i
    exact pullbackAction_fst (borelVariety G).toOver _ _
  rw [← incidenceOverIso_fst G i]
  infer_instance

private theorem simpleEndpoint_equivariant :
    letI := simpleBundleAction G i
    IsModHom (borelVariety G).toOver (simpleEndpointOver G i) := by
  let := simpleBundleAction G i
  let := incidenceAction G i
  let : IsModHom (borelVariety G).toOver (incidenceOverIso G i).hom :=
    incidenceOverIso_equivariant G i
  let : IsModHom (borelVariety G).toOver
      (pullback.snd (partialFlagMorphism G {i}) (partialFlagMorphism G {i})) := by
    let := partial_borel G i
    exact pullbackAction_snd (borelVariety G).toOver _ _
  rw [← incidenceOverIso_snd G i]
  infer_instance

private def overPullbackIso {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S : C} {A X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : A.left ≅ pullback f.left g.left)
    (ha : a.hom ≫ pullback.fst f.left g.left ≫ X.hom = A.hom) :
    A ≅ pullback f g := by
  let c := PreservesPullback.iso (Over.forget S) f g
  refine Over.isoMk (a ≪≫ c.symm) ?_
  change (a.hom ≫ c.inv) ≫ (pullback f g).hom = _
  rw [← (pullback.fst f g).w, ← Category.assoc, Category.assoc]
  have hcf := PreservesPullback.iso_inv_fst (Over.forget S) f g
  change c.inv ≫ (pullback.fst f g).left = pullback.fst f.left g.left at hcf
  simpa only [Category.assoc] using
    (congrArg (fun t => a.hom ≫ t ≫ X.hom) hcf).trans ha

private theorem overPullbackIso_snd {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S : C} {A X Y Z : Over S} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : A.left ≅ pullback f.left g.left)
    (ha : a.hom ≫ pullback.fst f.left g.left ≫ X.hom = A.hom) :
    (overPullbackIso f g a ha).hom.left ≫ (pullback.snd f g).left =
      a.hom ≫ pullback.snd f.left g.left := by
  let c := PreservesPullback.iso (Over.forget S) f g
  change (a.hom ≫ c.inv) ≫ (pullback.snd f g).left = _
  have hcs := PreservesPullback.iso_inv_snd (Over.forget S) f g
  change c.inv ≫ (pullback.snd f g).left = pullback.snd f.left g.left at hcs
  rw [Category.assoc, hcs]

private def bsdhEndpointOver (word : List G.rootBase.support) :
    (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (bsdhMap G word) rfl

private def appendRawIso (word : List G.rootBase.support) (j : G.rootBase.support) :
    (bsdhVariety G (word ++ [j])).toOver.left ≅
      pullback (bsdhEndpointOver G word).left (simpleProjectionOver G j).left :=
  (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word j)

private theorem appendRawIso_toSpec (word : List G.rootBase.support)
    (j : G.rootBase.support) :
    (appendRawIso G word j).hom ≫
      pullback.fst (bsdhEndpointOver G word).left (simpleProjectionOver G j).left ≫
        (bsdhVariety G word).toOver.hom = (bsdhVariety G (word ++ [j])).toOver.hom :=
  bsdhAppendFst_toSpec G word j

private def appendOverIso (word : List G.rootBase.support) (j : G.rootBase.support) :
    (bsdhVariety G (word ++ [j])).toOver ≅
      pullback (bsdhEndpointOver G word) (simpleProjectionOver G j) :=
  overPullbackIso (bsdhEndpointOver G word) (simpleProjectionOver G j)
    (appendRawIso G word j) (appendRawIso_toSpec G word j)

private theorem appendOverIso_endpoint (word : List G.rootBase.support)
    (j : G.rootBase.support) :
    (appendOverIso G word j).hom ≫
      pullback.snd (bsdhEndpointOver G word) (simpleProjectionOver G j) ≫
        simpleEndpointOver G j = bsdhEndpointOver G (word ++ [j]) := by
  apply (Over.forget (Spec (CommRingCat.of K))).map_injective
  change ((appendOverIso G word j).hom.left ≫
    (pullback.snd (bsdhEndpointOver G word) (simpleProjectionOver G j)).left) ≫
      (simpleEndpointOver G j).left = bsdhMap G (word ++ [j])
  dsimp only [appendOverIso]
  rw [overPullbackIso_snd]
  exact bsdhAppendIso_endpoint G word j

private theorem nil_map (q : (bsdhVariety G []).points) :
    Variety.mapPoints (bsdhEndpointOver G []) q = baseFlagPoint G := by
  apply Subtype.ext
  let l : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) := q.val
  change l ≫ (baseFlagPoint G).val = (baseFlagPoint G).val
  have hl : l = 𝟙 _ := by
    have h : l ≫ ((baseFlagPoint G).val ≫ (flagVariety G).toSpec) = 𝟙 _ := q.property
    rw [(baseFlagPoint G).property, Category.comp_id] at h
    exact h
  rw [hl, Category.id_comp]

private theorem base_fixed (b : (borelVariety G).points) :
    b • baseFlagPoint G = baseFlagPoint G := by
  rw [Variety.restricted_smul (borelInclusion G)]
  have hmem : Variety.mapPoints (borelInclusion G) b ∈
      (MulAction.stabilizer (reductiveVariety G).points (baseFlagPoint G) :
        Set (reductiveVariety G).points) := by
    rw [← borelInclusion_stabilizer G]
    exact ⟨b, rfl⟩
  exact hmem

private theorem exists_bsdh_action (word : List G.rootBase.support) :
    ∃ a : ModObj (borelVariety G).toOver (bsdhVariety G word).toOver,
      let := a
      IsModHom (borelVariety G).toOver (bsdhEndpointOver G word) := by
  induction word using List.reverseRecOn with
  | nil =>
    let a := ModObj.trivialAction (borelVariety G).toOver (bsdhVariety G []).toOver
    let := a
    refine ⟨a, ?_⟩
    apply Variety.isModHom_of_points (borelVariety G) (bsdhVariety G [])
      (flagVariety G) (bsdhEndpointOver G [])
    intro b q
    rw [nil_map, nil_map, base_fixed]
  | append_singleton word j ih =>
    obtain ⟨a, ha⟩ := ih
    let := a
    let := ha
    let := simpleBundleAction G j
    let := simpleProjection_equivariant G j
    let := simpleEndpoint_equivariant G j
    let := pullbackAction (borelVariety G).toOver
      (bsdhEndpointOver G word) (simpleProjectionOver G j)
    let := pullbackAction_snd (borelVariety G).toOver
      (bsdhEndpointOver G word) (simpleProjectionOver G j)
    let e := appendOverIso G word j
    let a' := ModObj.ofIso (Iso.refl (borelVariety G).toOver) e.symm
    let := a'
    have he : IsModHom (borelVariety G).toOver e.hom :=
      transport_inverse (borelVariety G).toOver e.symm
    let := he
    refine ⟨a', ?_⟩
    rw [← appendOverIso_endpoint G word j]
    infer_instance

/-- The Borel action on an iterated simple-Schubert scheme. -/
@[instance_reducible] def bsdhBorelAction (word : List G.rootBase.support) :
    ModObj (borelVariety G).toOver (bsdhVariety G word).toOver :=
  Classical.choose (exists_bsdh_action G word)

/-- The iterated endpoint commutes with the Borel action. -/
theorem bsdhBorelEquivariant (word : List G.rootBase.support) :
    letI := bsdhBorelAction G word
    IsModHom (borelVariety G).toOver (Over.homMk (bsdhMap G word) rfl :
      (bsdhVariety G word).toOver ⟶ (flagVariety G).toOver) :=
  Classical.choose_spec (exists_bsdh_action G word)

end SchubertGeometry
