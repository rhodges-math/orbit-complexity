import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine pushouts and cartesian spectrum squares
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

/-- A square of affine spectra is cartesian exactly when its ring square is a pushout. -/
theorem isPushout_iff_spec_pullback {A B C D : CommRingCat}
    (f : A ⟶ B) (g : A ⟶ C) (p : B ⟶ D) (q : C ⟶ D) :
    IsPushout f g p q ↔ IsPullback (Spec.map p) (Spec.map q) (Spec.map f) (Spec.map g) := by
  constructor
  · exact isPullback_SpecMap_of_isPushout f g p q
  · intro h
    have h' : IsPullback p.op q.op f.op g.op := h.of_map_of_faithful Scheme.Spec
    exact h'.flip.unop

end FrobeniusSplitting
