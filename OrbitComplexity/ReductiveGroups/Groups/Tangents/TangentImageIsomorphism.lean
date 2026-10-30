import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Tangent Image Isomorphism

The tangent image of a subgroup is independent of an isomorphic
presentation of its coordinate Hopf algebra. -/

noncomputable section
namespace ReductiveGroups

variable {K B A C : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [CommRing A] [HopfAlgebra K A] [CommRing C] [HopfAlgebra K C]

/-- Postcomposing a coordinate Hopf map with an equivalence does not change
the image of its differential inside the original tangent Lie algebra. -/
theorem tangentImage_comp_bialgEquiv
    (φ : B →ₐc[K] A) (e : A ≃ₐc[K] C) :
    (TauCeti.derivationCompLieHom (B := K) (e.toBialgHom.comp φ)).range =
      (TauCeti.derivationCompLieHom (B := K) φ).range := by
  have he : Function.Surjective
      (TauCeti.derivationCompLieHom (B := K) e.toBialgHom) := by
    intro d
    refine ⟨TauCeti.derivationCompLieHom (B := K) e.symm.toBialgHom d, ?_⟩
    rw [← LieHom.comp_apply, ← TauCeti.derivationCompLieHom_comp]
    have hid : e.symm.toBialgHom.comp e.toBialgHom = BialgHom.id K A :=
      BialgEquiv.symm_comp e
    rw [hid, TauCeti.derivationCompLieHom_id]
    rfl
  rw [TauCeti.derivationCompLieHom_comp]
  apply le_antisymm
  · intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact ⟨_, rfl⟩
  · intro x hx
    obtain ⟨d, rfl⟩ := hx
    obtain ⟨c, hc⟩ := he d
    refine ⟨c, ?_⟩
    change (TauCeti.derivationCompLieHom (B := K) φ)
      ((TauCeti.derivationCompLieHom (B := K) e.toBialgHom) c) =
        (TauCeti.derivationCompLieHom (B := K) φ) d
    rw [hc]

end ReductiveGroups
