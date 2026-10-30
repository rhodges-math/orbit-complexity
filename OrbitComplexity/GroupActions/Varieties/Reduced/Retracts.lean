import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties

/-! Reducedness descends along a scheme retraction. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GroupActions

/-- A retract of a reduced scheme is reduced. -/
theorem reduced_of_retraction {X Y : Scheme} (s : X ⟶ Y) (r : Y ⟶ X)
    (hs : s ≫ r = 𝟙 X) [IsReduced Y] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover ?_
  intro i
  let j := X.affineCover.f i
  let q := pullback.snd r j
  have : IsReduced (pullback r j) := isReduced_of_isOpenImmersion (pullback.fst r j)
  let t := pullback.lift (j ≫ s) (𝟙 (X.affineCover.X i))
    (show (j ≫ s) ≫ r = (𝟙 _) ≫ j by rw [Category.assoc, hs]; simp)
  have ht : t ≫ q = 𝟙 (X.affineCover.X i) := pullback.lift_snd _ _ _
  have hΓ : Scheme.Γ.map q.op ≫ Scheme.Γ.map t.op =
      𝟙 (Scheme.Γ.obj (op (X.affineCover.X i))) := by
    rw [← Functor.map_comp]
    change Scheme.Γ.map (t ≫ q).op = _
    rw [ht]
    exact Scheme.Γ.map_id _
  have hleft : Function.LeftInverse (Scheme.Γ.map t.op) (Scheme.Γ.map q.op) := by
    intro a
    exact congrArg (fun f : Scheme.Γ.obj (op (X.affineCover.X i)) ⟶
      Scheme.Γ.obj (op (X.affineCover.X i)) => f a) hΓ
  have : _root_.IsReduced (Scheme.Γ.obj (op (pullback r j))) := by
    change _root_.IsReduced Γ(pullback r j, ⊤)
    infer_instance
  have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    isReduced_of_injective (Scheme.Γ.map q.op).hom hleft.injective
  exact isReduced_of_isAffine_isReduced (X := X.affineCover.X i)

end GroupActions
