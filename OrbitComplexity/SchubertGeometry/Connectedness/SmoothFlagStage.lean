import OrbitComplexity.FrobeniusSplitting.Normality.Limits.SmoothCartesianStages
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import OrbitComplexity.SchubertGeometry.FlagVariety.Properties
import Batteries.Tactic.Lint

/-! # Smooth field fibres of the arithmetic flag model

The Cartesian flag comparison gives smoothness at a later coefficient stage.
Every field fibre of that same flag model has integrally closed domain stalks.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting ReductiveGroups

namespace SchubertGeometry

universe u

private theorem smooth_flag_fibre_stalks {B : Scheme.{u}}
    (F : Over B) [Smooth F.hom]
    (L : Type u) [Field L] (s : Spec (.of L) ⟶ B) :
    ∀ x : (pullback s F.hom : Scheme.{u}),
      IsDomain ((pullback s F.hom : Scheme.{u}).presheaf.stalk x) ∧
        IsIntegrallyClosed ((pullback s F.hom : Scheme.{u}).presheaf.stalk x) := by
  exact stalks_of_smooth (pullback.fst s F.hom)

/-- The prescribed arithmetic flag model acquires normal field-fibre stalks
above any coefficient stage, preserving its Cartesian comparison and projection. -/
theorem exists_smooth_flag_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K) (hS : S.FG)
    (F : Over (Spec (.of S))) [CompactSpace F.left]
    [LocallyOfFinitePresentation F.hom]
    (q : (flagVariety G).scheme ⟶ F.left)
    (hq : IsPullback q (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ t : CoefficientStage S, start ≤ t ∧
      Smooth (stageScalarModel S F.hom t).hom ∧
      (∃ qt : (flagVariety G).scheme ⟶ (stageScalarModel S F.hom t).left,
        IsPullback qt (flagVariety G).toSpec (stageScalarModel S F.hom t).hom
          (Spec.map (CommRingCat.ofHom (algebraMap t.val K))) ∧
        qt ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom
            (Subalgebra.inclusion t.property.2).toRingHom)) F.hom = q) ∧
      ∀ (L : Type u) [Field L]
        (s : Spec (.of L) ⟶ Spec (.of t.val)),
        ∀ x : (pullback s (stageScalarModel S F.hom t).hom : Scheme.{u}),
          IsDomain ((pullback s (stageScalarModel S F.hom t).hom :
            Scheme.{u}).presheaf.stalk x) ∧
          IsIntegrallyClosed ((pullback s (stageScalarModel S F.hom t).hom :
            Scheme.{u}).presheaf.stalk x) := by
  let : Smooth (flagVariety G).toOver.hom :=
    (inferInstance : Smooth (flagVariety G).toSpec)
  obtain ⟨t, ht, hs, qt, hqt, hproj⟩ :=
    exists_smooth_cartesian_stage S hS F (flagVariety G).toOver q hq start
  let : Smooth (stageScalarModel S F.hom t).hom := hs
  exact ⟨t, ht, hs, ⟨qt, hqt, hproj⟩,
    fun L _ s => smooth_flag_fibre_stalks (stageScalarModel S F.hom t) L s⟩

end SchubertGeometry
