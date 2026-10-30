import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Batteries.Tactic.Lint

/-!
# Scalar squares on overlaps

The map between two prescribed pairwise pullbacks is Cartesian over the
base whenever the chart squares are Cartesian.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

/-- The constructed map on chart overlaps retains the prescribed scalar square. -/
theorem scalarOverlap_isPullback {C : Type u} [Category.{v} C] [HasPullbacks C]
    {A B Y AK BK YK S SK : C}
    (f : A ⟶ Y) (g : B ⟶ Y) (fK : AK ⟶ YK) (gK : BK ⟶ YK)
    (u : AK ⟶ A) (v : BK ⟶ B) (z : YK ⟶ Y)
    (hu : u ≫ f = fK ≫ z) (hv : v ≫ g = gK ≫ z)
    (pA : A ⟶ S) (pAK : AK ⟶ SK) (beta : SK ⟶ S)
    (hA : IsPullback u pAK pA beta) (hB : IsPullback v gK g z) :
    IsPullback
      (pullback.map fK gK f g u v z hu.symm hv.symm)
      (pullback.fst fK gK ≫ pAK) (pullback.fst f g ≫ pA) beta := by
  let k : pullback fK gK ⟶ pullback f g :=
    pullback.map fK gK f g u v z hu.symm hv.symm
  have hout : IsPullback (pullback.fst fK gK)
      (k ≫ pullback.snd f g) (u ≫ f) g := by
    have h := (IsPullback.of_hasPullback fK gK).paste_vert hB.flip
    simpa only [k, pullback.lift_snd, hu] using h
  have htop : IsPullback (pullback.fst fK gK) k u (pullback.fst f g) :=
    IsPullback.of_bot hout (by simp only [k, pullback.lift_fst])
      (IsPullback.of_hasPullback f g)
  exact htop.flip.paste_vert hA

end FrobeniusSplitting
