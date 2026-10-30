import OrbitComplexity.SchubertGeometry.Parabolics.Preimage
import OrbitComplexity.FrobeniusSplitting.Normality.FlatDescent
import OrbitComplexity.SchubertGeometry.Normality.PositiveResolutionFibres

/-! # Normal stalks under the parabolic Schubert projection -/

noncomputable section

namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- Normal stalks of the complete-flag Schubert preimage descend to the partial
Schubert variety along the smooth, surjective parabolic projection. -/
theorem partialSchubert_stalks_of_full (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w)
    (hfull : ∀ x : (schubertVariety G
        (w * longestParabolicElement G.rootBase J)).scheme,
      IsDomain ((schubertVariety G
          (w * longestParabolicElement G.rootBase J)).scheme.presheaf.stalk x) ∧
        IsIntegrallyClosed ((schubertVariety G
          (w * longestParabolicElement G.rootBase J)).scheme.presheaf.stalk x)) :
    ∀ y : (partialSchubertVariety G J w).scheme,
      IsDomain ((partialSchubertVariety G J w).scheme.presheaf.stalk y) ∧
        IsIntegrallyClosed ((partialSchubertVariety G J w).scheme.presheaf.stalk y) := by
  obtain ⟨e, _⟩ := (partialSchubert_pullback G J w hw).2
  let p := (partialFlagMorphism G J).left
  let j := (partialSchubertInclusion G J w).left
  let f : (schubertVariety G (w * longestParabolicElement G.rootBase J)).scheme ⟶
      (partialSchubertVariety G J w).scheme := e.hom ≫ pullback.snd p j
  let : Smooth p := partialFlagMorphism_smooth G J
  let : Surjective p := by dsimp [p]; infer_instance
  let : Flat f := by dsimp [f]; infer_instance
  let : Surjective f := by dsimp [f]; infer_instance
  exact FrobeniusSplitting.stalks_of_flat_surjective f hfull

/-- A Schubert variety in a partial flag variety has integrally closed local
domains for every minimal parabolic coset representative. -/
theorem partialSchubert_normal_stalks {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (J : Set G.rootBase.support) (w : G.weylGroup)
    (hw : IsMinimalRightParabolic G.rootBase J w) :
    ∀ y : (partialSchubertVariety G J w).scheme,
      IsDomain ((partialSchubertVariety G J w).scheme.presheaf.stalk y) ∧
        IsIntegrallyClosed ((partialSchubertVariety G J w).scheme.presheaf.stalk y) := by
  exact @partialSchubert_stalks_of_full.{u} K kField kClosed kZero G J w hw
    (@schubert_normal_stalks.{u} K kField kClosed kZero G
      (w * longestParabolicElement G.rootBase J))

end SchubertGeometry
