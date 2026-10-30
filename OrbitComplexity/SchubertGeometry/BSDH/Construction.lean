import OrbitComplexity.SchubertGeometry.FlagBundle.Connected
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoConnected
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import OrbitComplexity.SchubertGeometry.FlagBundle.Maps
import OrbitComplexity.SchubertGeometry.FlagBundle.Smooth
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoSmooth
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoProperties

/-! # Iterated simple-Schubert correspondence schemes

Starting from the base flag, each appended simple root adds the pullback of its
projective-line flag bundle. The corresponding endpoint maps define schemes over
the flag variety, with proper, smooth and geometrically connected structure maps.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem base_geomConnected :
    GeometricallyConnected (𝟙 (Spec (CommRingCat.of K))) := by
  constructor
  intro F hF y Z f g h
  have : IsIso g := by
    rw [← h.isoPullback_hom_snd]
    infer_instance
  exact g.homeomorph.connectedSpace_iff.mpr inferInstance

private abbrev simpleFibre (i : G.rootBase.support) : GroupActions.Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private abbrev simpleProjection (i : G.rootBase.support) :
    flagBundleScheme G (simpleFibre G i) ⟶ (flagVariety G).scheme :=
  flagBundleProjection G (simpleFibre G i)

private abbrev simpleEndpoint (i : G.rootBase.support) :
    flagBundleScheme G (simpleFibre G i) ⟶ (flagVariety G).scheme :=
  flagBundleMap G (simpleFibre G i)
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private def bsdhStage : List G.rootBase.support → Over (flagVariety G).scheme
  | [] => Over.mk (baseFlagPoint G).val
  | i :: word =>
    Over.mk (pullback.snd (bsdhStage word).hom (simpleProjection G i) ≫ simpleEndpoint G i)

private theorem bsdhStage_isProper (word : List G.rootBase.support) :
    IsProper ((bsdhStage G word).hom ≫ (flagVariety G).toSpec) := by
  induction word with
  | nil =>
    change IsProper ((baseFlagPoint G).val ≫ (flagVariety G).toSpec)
    rw [(baseFlagPoint G).property]
    infer_instance
  | cons i word ih =>
    change IsProper ((pullback.snd (bsdhStage G word).hom (simpleProjection G i) ≫
      simpleEndpoint G i) ≫ (flagVariety G).toSpec)
    rw [Category.assoc, flagBundleMap_toSpec, ← Category.assoc,
      ← pullback.condition, Category.assoc]
    let := ih
    have : IsProper (simpleProjection G i) :=
      flagBundleProjection_isProper G (simpleFibre G i)
    infer_instance

private theorem bsdhStage_smooth (word : List G.rootBase.support) :
    Smooth ((bsdhStage G word).hom ≫ (flagVariety G).toSpec) := by
  induction word with
  | nil =>
    change Smooth ((baseFlagPoint G).val ≫ (flagVariety G).toSpec)
    rw [(baseFlagPoint G).property]
    infer_instance
  | cons i word ih =>
    change Smooth ((pullback.snd (bsdhStage G word).hom (simpleProjection G i) ≫
      simpleEndpoint G i) ≫ (flagVariety G).toSpec)
    rw [Category.assoc, flagBundleMap_toSpec, ← Category.assoc,
      ← pullback.condition, Category.assoc]
    let := ih
    have : Smooth (simpleProjection G i) :=
      flagBundleProjection_smooth G (simpleFibre G i)
    infer_instance

private theorem bsdhStage_geomConnected (word : List G.rootBase.support) :
    GeometricallyConnected ((bsdhStage G word).hom ≫ (flagVariety G).toSpec) := by
  induction word with
  | nil =>
    change GeometricallyConnected ((baseFlagPoint G).val ≫ (flagVariety G).toSpec)
    rw [(baseFlagPoint G).property]
    exact base_geomConnected
  | cons i word ih =>
    change GeometricallyConnected
      ((pullback.snd (bsdhStage G word).hom (simpleProjection G i) ≫
        simpleEndpoint G i) ≫ (flagVariety G).toSpec)
    rw [Category.assoc, flagBundleMap_toSpec, ← Category.assoc,
      ← pullback.condition, Category.assoc]
    let := ih
    have : Smooth ((bsdhStage G word).hom ≫ (flagVariety G).toSpec) :=
      bsdhStage_smooth G word
    have : Smooth (simpleProjection G i) :=
      flagBundleProjection_smooth G (simpleFibre G i)
    have : GeometricallyConnected (simpleProjection G i) :=
      flagBundle_geometricallyConnected G (simpleFibre G i)
    exact GeometricallyConnected.comp
      (pullback.fst (bsdhStage G word).hom (simpleProjection G i))
      ((bsdhStage G word).hom ≫ (flagVariety G).toSpec)

/-- The iterated simple-Schubert correspondence scheme for an ordered word of simple roots. -/
def bsdhScheme (word : List G.rootBase.support) : Scheme :=
  (bsdhStage G word.reverse).left

/-- The endpoint morphism from an iterated simple-Schubert scheme to the flag variety. -/
def bsdhMap (word : List G.rootBase.support) :
    bsdhScheme G word ⟶ (flagVariety G).scheme := (bsdhStage G word.reverse).hom

/-- The structure morphism of an iterated simple-Schubert scheme over the coefficient field. -/
def bsdhToSpec (word : List G.rootBase.support) :
    bsdhScheme G word ⟶ Spec (CommRingCat.of K) := bsdhMap G word ≫ (flagVariety G).toSpec

/-- An iterated simple-Schubert scheme is proper over the coefficient field. -/
instance bsdh_isProper (word : List G.rootBase.support) : IsProper (bsdhToSpec G word) :=
  bsdhStage_isProper G word.reverse

/-- An iterated simple-Schubert scheme is smooth over the coefficient field. -/
instance bsdh_smooth (word : List G.rootBase.support) : Smooth (bsdhToSpec G word) :=
  bsdhStage_smooth G word.reverse

/-- The endpoint morphism to the flag variety is proper. -/
instance bsdhMap_isProper (word : List G.rootBase.support) : IsProper (bsdhMap G word) := by
  have : IsProper (bsdhMap G word ≫ (flagVariety G).toSpec) := bsdh_isProper G word
  exact IsProper.of_comp (bsdhMap G word) (flagVariety G).toSpec

/-- An iterated simple-Schubert scheme has connected geometric fibres over the field. -/
instance bsdh_geomConnected (word : List G.rootBase.support) :
    GeometricallyConnected (bsdhToSpec G word) := bsdhStage_geomConnected G word.reverse

/-- Appending a simple root is the pullback of its flag bundle, with the new endpoint. -/
def bsdhAppendIso (word : List G.rootBase.support) (i : G.rootBase.support) :
    Over.mk (bsdhMap G (word ++ [i])) ≅
      Over.mk (pullback.snd (bsdhMap G word)
        (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ≫
            flagBundleMap G
              (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
              (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) := by
  change bsdhStage G (word ++ [i]).reverse ≅ _
  rw [List.reverse_append]
  exact Iso.refl _

/-- The projection deleting the last simple-Schubert correspondence from an appended word. -/
def bsdhAppendFst (word : List G.rootBase.support) (i : G.rootBase.support) :
    bsdhScheme G (word ++ [i]) ⟶ bsdhScheme G word :=
  (bsdhAppendIso G word i).hom.left ≫ pullback.fst _ _

/-- The append isomorphism intertwines the bundle endpoint and the iterated endpoint. -/
theorem bsdhAppendIso_endpoint (word : List G.rootBase.support) (i : G.rootBase.support) :
    (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word)
          (flagBundleProjection G
            (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) ≫
        flagBundleMap G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) =
      bsdhMap G (word ++ [i]) :=
  (bsdhAppendIso G word i).hom.w

/-- Deleting the last correspondence preserves the structure morphism to the field. -/
theorem bsdhAppendFst_toSpec (word : List G.rootBase.support) (i : G.rootBase.support) :
    bsdhAppendFst G word i ≫ bsdhToSpec G word = bsdhToSpec G (word ++ [i]) := by
  have hp := congrArg (fun f => (bsdhAppendIso G word i).hom.left ≫
    f ≫ (flagVariety G).toSpec)
    (pullback.condition (f := bsdhMap G word) (g := simpleProjection G i))
  have hq := congrArg (fun f => (bsdhAppendIso G word i).hom.left ≫
    pullback.snd (bsdhMap G word) (simpleProjection G i) ≫ f)
    (flagBundleMap_toSpec G (simpleFibre G i)
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)))
  have he := congrArg (fun f => f ≫ (flagVariety G).toSpec)
    (bsdhAppendIso_endpoint G word i)
  simp only [Category.assoc] at hp hq he
  exact hp.trans (hq.symm.trans he)

/-- The projection deleting the last simple-Schubert correspondence is proper. -/
instance bsdhAppendFst_isProper (word : List G.rootBase.support) (i : G.rootBase.support) :
    IsProper (bsdhAppendFst G word i) := by
  have : IsIso (bsdhAppendIso G word i).hom.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (bsdhAppendIso G word i)).hom))
  dsimp only [bsdhAppendFst]
  have : IsProper (simpleProjection G i) :=
    flagBundleProjection_isProper G (simpleFibre G i)
  infer_instance

/-- The projection deleting the last simple-Schubert correspondence is smooth. -/
instance bsdhAppendFst_smooth (word : List G.rootBase.support) (i : G.rootBase.support) :
    Smooth (bsdhAppendFst G word i) := by
  have : IsIso (bsdhAppendIso G word i).hom.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (bsdhAppendIso G word i)).hom))
  dsimp only [bsdhAppendFst]
  have : Smooth (simpleProjection G i) :=
    flagBundleProjection_smooth G (simpleFibre G i)
  infer_instance

end SchubertGeometry
