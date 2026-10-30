import Batteries.Tactic.Lint

/-! # Chart data with dependent indices

Equality of the base indices transports both chart indices and their common relation.
-/

set_option autoImplicit false
set_option maxHeartbeats 50000

universe u v w

namespace SchubertGeometry.RetainedCharacter

private theorem dependent_chart_data_transport
    {I : Sort u} (A : I → Sort v) (B : I → Sort w)
    (D : ∀ i, A i → B i → Prop)
    (original input : I) (hInputs : input = original)
    (π : A original) (jK : B original) (hData : D original π jK) :
    ∃ (π' : A input) (jK' : B input),
      HEq π' π ∧ HEq jK' jK ∧ D input π' jK' := by
  cases hInputs
  exact ⟨π, jK, HEq.rfl, HEq.rfl, hData⟩

end SchubertGeometry.RetainedCharacter
