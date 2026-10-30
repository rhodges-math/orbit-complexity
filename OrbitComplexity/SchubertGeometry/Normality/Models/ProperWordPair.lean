import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ProperAppend
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelScalarExtension
import Batteries.Tactic.Lint

/-! # Two proper word models on one prescribed coefficient extension

The second word is constructed above the first word's coefficient ring. The
first word is then extended , retaining its scalar square.
All coefficient choices precede field fibres and preserve the prescribed base.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry

noncomputable section

universe u

/-- Construct both proper, smooth, geometrically connected word models
on one finitely generated ring above the entire prescribed coefficient ring. -/
theorem exists_proper_word_pair {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (a b : List G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ R : Subalgebra ℤ K, S ≤ R ∧ R.FG ∧
      ∃ (A B : Scheme.{u}) (baseA : A ⟶ Spec (.of R)) (baseB : B ⟶ Spec (.of R))
        (mA : bsdhScheme G a ⟶ A) (mB : bsdhScheme G b ⟶ B),
        IsProper baseA ∧ Smooth baseA ∧ GeometricallyConnected baseA ∧
        IsProper baseB ∧ Smooth baseB ∧ GeometricallyConnected baseB ∧
        IsPullback mA (bsdhToSpec G a) baseA
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        IsPullback mB (bsdhToSpec G b) baseB
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨T, hST, hT, A₀, a₀, m₀, hp₀, hs₀, hg₀, h₀⟩ :=
    exists_proper_bsdh_model G a S hS
  obtain ⟨R, hTR, hR, B, baseB, mB, hpB, hsB, hgB, hB⟩ :=
    exists_proper_bsdh_model G b T hT
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : IsProper a₀ := hp₀
  let : Smooth a₀ := hs₀
  let : GeometricallyConnected a₀ := hg₀
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap T R))
  let A := pullback a₀ ρ
  let baseA := pullback.snd a₀ ρ
  obtain ⟨mA, hA, _, _, _⟩ :=
    FrobeniusSplitting.model_scalar_extension (R := R) a₀ (bsdhToSpec G a) m₀ h₀
  refine ⟨R, hST.trans hTR, hR, A, B, baseA, baseB, mA, mB,
    ?_, ?_, ?_, hpB, hsB, hgB, hA, hB⟩ <;> infer_instance

end
end SchubertGeometry
