import Mathlib.AlgebraicGeometry.Pullbacks
import Batteries.Tactic.Lint

/-! # Scalar comparison on open subschemes

Restricting a Cartesian square to an open subscheme gives a scalar
comparison of the open subschemes, with its projection equation.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u

/-- The inverse image of a model open in a Cartesian comparison is isomorphic
over the new base to its scalar pullback, preserving the original projection. -/
theorem exists_scalar_open_iso {B T : Scheme.{u}} (κ : T ⟶ B)
    (X : Over T) (Y : Over B) (q : X.left ⟶ Y.left)
    (h : IsPullback q X.hom Y.hom κ)
    (U : Y.left.Opens) (V : X.left.Opens) (hV : q ⁻¹ᵁ U = V) :
    ∃ E : Over.mk (V.ι ≫ X.hom) ≅
      Over.mk (pullback.fst κ (U.ι ≫ Y.hom)),
      E.hom.left ≫ pullback.snd κ (U.ι ≫ Y.hom) ≫ U.ι = V.ι ≫ q := by
  subst V
  have hU : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ X.hom)
      (U.ι ≫ Y.hom) κ := (isPullback_morphismRestrict q U).paste_vert h
  let E := hU.flip.isoOverPullback
  refine ⟨E, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ U.ι) hU.flip.isoOverPullback_hom_left_comp_snd).trans
      (morphismRestrict_ι q U))

end FrobeniusSplitting
