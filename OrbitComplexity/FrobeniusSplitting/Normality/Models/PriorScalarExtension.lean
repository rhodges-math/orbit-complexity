import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorPatchCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The prior scheme and every prior chart under coefficient extension -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting

private theorem chart_comparison {W Y YK YR : Scheme.{u}}
    (a : W ⟶ Y) (qK : YK ⟶ Y) (qR : YR ⟶ Y) (m : YK ⟶ YR)
    (hm : m ≫ qR = qK) :
    ∃ d : pullback a qK ⟶ pullback a qR,
      d ≫ pullback.fst a qR = pullback.fst a qK ∧
      d ≫ pullback.snd a qR = pullback.snd a qK ≫ m ∧
      IsPullback d (pullback.snd a qK) (pullback.snd a qR) m := by
  let d : pullback a qK ⟶ pullback a qR :=
    pullback.map a qK a qR (𝟙 W) m (𝟙 Y) (by simp) (by simpa using hm.symm)
  have hf : d ≫ pullback.fst a qR = pullback.fst a qK := by simp [d]
  have hs : d ≫ pullback.snd a qR = pullback.snd a qK ≫ m := by simp [d]
  have H : IsPullback (d ≫ pullback.fst a qR) (pullback.snd a qK) a (m ≫ qR) := by
    rw [hf, hm]
    exact IsPullback.of_hasPullback a qK
  exact ⟨d, hf, hs, H.of_right hs (IsPullback.of_hasPullback a qR)⟩

/-- Coefficient extension preserves the prior scheme and its properness, and
all prior chart comparisons are cartesian with both projection equations. -/
theorem exists_prior_scalar_extension {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {Y YK : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : YK ⟶ Spec (.of K)) (qY : YK ⟶ Y)
    (h : IsPullback qY baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    ∃ m : YK ⟶ YR,
      IsProper baseR ∧ IsPullback m baseK baseR kr ∧ m ≫ qR = qY ∧
      m ≫ baseR = baseK ≫ kr ∧
      ∀ (W : Scheme.{u}) (a : W ⟶ Y),
        ∃ d : pullback a qY ⟶ pullback a qR,
          d ≫ pullback.fst a qR = pullback.fst a qY ∧
          d ≫ pullback.snd a qR = pullback.snd a qY ≫ m ∧
          IsPullback d (pullback.snd a qY ≫ baseK) (pullback.snd a qR ≫ baseR) kr := by
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let kr := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hcoeff : kr ≫ sr = Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have H : IsPullback qY baseK base (kr ≫ sr) := by rw [hcoeff]; exact h
  let T := IsPullback.of_hasPullback base sr
  let m := T.lift qY (baseK ≫ kr) (by simpa only [Category.assoc] using H.w)
  have hm : m ≫ pullback.fst base sr = qY := T.lift_fst _ _ _
  have hb : m ≫ pullback.snd base sr = baseK ≫ kr := T.lift_snd _ _ _
  have HP : IsPullback m baseK (pullback.snd base sr) kr := IsPullback.of_right' H T
  refine ⟨m, inferInstance, HP, hm, hb, fun W a ↦ ?_⟩
  obtain ⟨d, hf, hs, hd⟩ := chart_comparison a qY (pullback.fst base sr) m hm
  exact ⟨d, hf, hs, hd.paste_vert HP⟩

end FrobeniusSplitting
