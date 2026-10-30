import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel

/-!
# Surjective Bialgebra Descent

Descent of bialgebra morphisms along a surjective coordinate morphism. -/

noncomputable section

namespace ReductiveGroups

variable {K A B C : Type*} [Field K]
  [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]
  [CommRing C] [HopfAlgebra K C]

private theorem surjectiveBialgebra_ker_le
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] C) (hker : ∀ a : A, ρ a = 0 → φ a = 0) :
    (TauCeti.HopfIdeal.kerOfSurjective ρ hρ).toIdeal ≤
      RingHom.ker (φ : A →ₐ[K] C) := by
  intro a ha
  rw [RingHom.mem_ker]
  exact hker a ((TauCeti.HopfIdeal.mem_kerOfSurjective ρ hρ).mp ha)

/-- A bialgebra morphism killing the kernel of a surjective morphism descends
to the original target, via its Hopf-ideal kernel quotient. -/
def surjectiveBialgebraDescend
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] C) (hker : ∀ a : A, ρ a = 0 → φ a = 0) : B →ₐc[K] C :=
  (Bialgebra.Quotient.liftBialgHom
    (TauCeti.HopfIdeal.kerOfSurjective ρ hρ).toIdeal φ
      (surjectiveBialgebra_ker_le ρ hρ φ hker)).comp
    (TauCeti.HopfIdeal.kerLiftBialgEquiv ρ hρ).symm.toBialgHom

/-- Descent composed with the original surjection recovers the given map. -/
theorem surjectiveBialgebraDescend_comp
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] C) (hker : ∀ a : A, ρ a = 0 → φ a = 0) :
    (surjectiveBialgebraDescend ρ hρ φ hker).comp ρ = φ := by
  ext a
  let I := TauCeti.HopfIdeal.kerOfSurjective ρ hρ
  let e := TauCeti.HopfIdeal.kerLiftBialgEquiv ρ hρ
  have he : e (Ideal.Quotient.mkₐ K I.toIdeal a) = ρ a := by
    exact TauCeti.HopfIdeal.kerLiftBialgHom_mk ρ hρ a
  change (Bialgebra.Quotient.liftBialgHom I.toIdeal φ
    (surjectiveBialgebra_ker_le ρ hρ φ hker))
    (e.symm (ρ a)) = φ a
  rw [← he, e.symm_apply_apply]
  exact Bialgebra.Quotient.liftBialgHom_mk I.toIdeal φ _ a

/-- The descended morphism is the unique one with this composite. -/
theorem surjectiveBialgebraDescend_unique
    (ρ : A →ₐc[K] B) (hρ : Function.Surjective ρ)
    (φ : A →ₐc[K] C) (hker : ∀ a : A, ρ a = 0 → φ a = 0)
    (ψ : B →ₐc[K] C) (hψ : ψ.comp ρ = φ) :
    ψ = surjectiveBialgebraDescend ρ hρ φ hker := by
  ext b
  obtain ⟨a, rfl⟩ := hρ b
  have h := congrArg (fun f : A →ₐc[K] C => f a) hψ
  have hd := congrArg (fun f : A →ₐc[K] C => f a)
    (surjectiveBialgebraDescend_comp ρ hρ φ hker)
  exact (by simpa only [BialgHom.comp_apply] using h.trans hd.symm)

end ReductiveGroups
