import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ProperAppend
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralSource

/-! # Integral normal field fibres of the constructed word model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReductiveGroups
noncomputable section
universe u
namespace SchubertGeometry

/-- The recursively constructed word model has integral normal field fibres.
The coefficient ring and the comparison are chosen before the field. -/
theorem exists_integral_bsdh_model {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ (R : Subalgebra ℤ K), S ≤ R ∧ R.FG ∧
      ∃ (Y : Scheme.{u}) (base : Y ⟶ Spec (.of R))
        (m : bsdhScheme G word ⟶ Y),
        IsProper base ∧ Smooth base ∧ GeometricallyConnected base ∧
        IsPullback m (bsdhToSpec G word) base
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of R)),
          IsProper (pullback.snd base t) ∧ Smooth (pullback.snd base t) ∧
          IsIntegral (pullback base t) ∧
          ∀ x : (pullback base t : Scheme.{u}),
            IsDomain ((pullback base t).presheaf.stalk x) ∧
              IsIntegrallyClosed ((pullback base t).presheaf.stalk x) := by
  obtain ⟨R, hSR, hR, Y, base, m, hproper, hsmooth, hconnected, hm⟩ :=
    exists_proper_bsdh_model G word S hS
  let : IsProper base := hproper
  let : Smooth base := hsmooth
  let : GeometricallyConnected base := hconnected
  refine ⟨R, hSR, hR, Y, base, m, hproper, hsmooth, hconnected, hm, ?_⟩
  intro L _ t
  let fibreBase := pullback.snd base t
  let : IsProper fibreBase := inferInstance
  let : Smooth fibreBase := inferInstance
  let : GeometricallyConnected fibreBase := inferInstance
  let : IsLocallyNoetherian (pullback base t) :=
    LocallyOfFiniteType.isLocallyNoetherian fibreBase
  have hnormal := FrobeniusSplitting.stalks_of_smooth fibreBase
  have hfibre : IsIntegral (pullback base t) :=
    FrobeniusSplitting.isIntegral_of_proper fibreBase (fun x ↦ (hnormal x).1)
  exact ⟨inferInstance, inferInstance, hfibre, hnormal⟩

end SchubertGeometry
