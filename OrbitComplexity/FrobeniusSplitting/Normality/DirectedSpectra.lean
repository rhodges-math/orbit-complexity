import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ColimitCovers
import OrbitComplexity.FrobeniusSplitting.Normality.AffinePushouts
import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Directed covers from algebra pushout refinements
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- Pushout refinements in an algebra diagram make its spectra locally directed. -/
theorem specs_locallyDirected {C : Type u} [Category.{u} C]
    {R : Type u} [CommRing R] (D : C ⥤ CommAlgCat.{u} R)
    (hrefine : ∀ (i j k : C) (fi : k ⟶ i) (fj : k ⟶ j),
      ∃ (l : C) (gi : i ⟶ l) (gj : j ⟶ l),
        IsPushout (CommRingCat.ofHom (D.map fi).hom.toRingHom)
          (CommRingCat.ofHom (D.map fj).hom.toRingHom)
          (CommRingCat.ofHom (D.map gi).hom.toRingHom)
          (CommRingCat.ofHom (D.map gj).hom.toRingHom)) :
    ((D.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := by
  apply locallyDirected_of_pullbacks
  intro i j k fi fj
  obtain ⟨l, gi, gj, hcart⟩ := hrefine i.unop j.unop k.unop fi.unop fj.unop
  refine ⟨Opposite.op l, gi.op, gj.op, ?_⟩
  exact (isPushout_iff_spec_pullback _ _ _ _).mp hcart

end FrobeniusSplitting
