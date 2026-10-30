import OrbitComplexity.FrobeniusSplitting.Splittings.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.SimpleRing.Basic
import Batteries.Tactic.Lint

/-! # Frobenius splittings of fields

A linear retraction of Frobenius gives a splitting over an arbitrary field of
positive characteristic, without a perfectness hypothesis.
-/

namespace FrobeniusSplitting.RingSplitting

private theorem field_linear_retraction {K S : Type*} [Field K] [CommRing S]
    [Nontrivial S] (f : K →+* S) :
    ∃ g : S →+ K, (∀ a b, g (f a * b) = a * g b) ∧ g 1 = 1 := by
  let : Module K S := Module.compHom S f
  let F : K →ₗ[K] S := Module.compHom.toLinearMap f
  have hF : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr f.injective
  obtain ⟨g, hg⟩ := F.exists_leftInverse_of_injective hF
  have hleft (a : K) : g (f a) = a := by
    exact congrArg (fun h : K →ₗ[K] K => h a) hg
  refine ⟨g.toAddMonoidHom, ?_, ?_⟩
  · intro a b
    exact g.map_smul a b
  · change g 1 = 1
    simpa only [f.map_one] using hleft (1 : K)

/-- Every field of exponential characteristic `p` admits a Frobenius splitting. -/
noncomputable def ofField (K : Type*) [Field K] (p : ℕ) [ExpChar K p] :
    RingSplitting K p := by
  classical
  let h := field_linear_retraction (frobenius K p)
  exact
    { toAddMonoidHom := h.choose
      map_pow_mul' := h.choose_spec.1
      map_one' := h.choose_spec.2 }

end FrobeniusSplitting.RingSplitting
