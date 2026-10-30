import OrbitComplexity.SchubertGeometry.BSDH.Construction

/-! # The specified coefficient model of the empty Bott--Samelson word -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReductiveGroups GroupActions
noncomputable section
universe u
namespace SchubertGeometry

/-- The empty word has the coefficient point as a proper smooth model with
geometrically connected fibres and its scalar comparison. -/
theorem bsdh_empty_model {K S : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing S] [Algebra S K] (G : ReductiveGroupData K) :
    ∃ (Y : Scheme.{u}) (base : Y ⟶ Spec (.of S))
      (m : bsdhScheme G [] ⟶ Y),
      IsProper base ∧ Smooth base ∧ GeometricallyConnected base ∧
      IsPullback m (bsdhToSpec G []) base
        (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
  have hnil : bsdhToSpec G [] = 𝟙 (Spec (.of K)) := by
    change (baseFlagPoint G).val ≫ (flagVariety G).toSpec = _
    exact (baseFlagPoint G).property
  have hgc : GeometricallyConnected (𝟙 (Spec (.of S))) := by
    constructor
    intro L _ t Z fst snd h
    let : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.connectedSpace_iff.mpr inferInstance
  refine ⟨Spec (.of S), 𝟙 _, Spec.map (CommRingCat.ofHom (algebraMap S K)),
    inferInstance, inferInstance, hgc, ?_⟩
  rw [hnil]
  exact IsPullback.of_id_snd

end SchubertGeometry
