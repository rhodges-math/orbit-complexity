import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps

/-!
# Anchors and scalar cone comparisons

A section of a cell model and a map from that cell define an anchor over the
coefficient stage. Generic transport compares this anchor with a specified point
in a Cartesian target model.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace FrobeniusSplitting

universe u

/-- A section followed by a morphism over the base defines an anchor from any
object over that same base. -/
def anchorArrow {T : Type*} [Category T] {B : T} (U : Over B)
    {X Y : Over B} (s : B ⟶ X.left) (hs : s ≫ X.hom = 𝟙 B) (f : X ⟶ Y) : U ⟶ Y :=
  Over.homMk (U.hom ≫ s) (by rw [Category.assoc, hs, Category.comp_id]) ≫ f

/-- The scalar cone retains the structural morphism to the coefficient stage. -/
theorem modelScalarCone_base {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) (i : CoefficientStage S) :
    (modelScalarCone S a).π.app (op i) ≫ (stageScalarModel S a i).hom =
      (genericScalarModel S a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap i.val K)) := by
  change pullback.lift _ _ _ ≫ pullback.fst _ a = _
  exact pullback.lift_fst _ _ _

/-- A scheme comparison for a section induces the full anchor-arrow comparison.
The two descriptions of the target isomorphism are identified as whole terms. -/
theorem anchorArrow_comparison {T : Type*} [Category T] {B B' : T}
    (U : Over B) (U' : Over B') {X Y : Over B'} {Z Z' : Over B}
    (E₀ E₁ : Z ≅ Z') (hE : E₀ = E₁)
    (s : B' ⟶ X.left) (hs : s ≫ X.hom = 𝟙 B') (f : X ⟶ Y)
    {a : U' ⟶ Y} (ha : a = anchorArrow U' s hs f)
    {t : U ⟶ Over.mk (𝟙 B)} {v : Over.mk (𝟙 B) ⟶ Z} {g : U ⟶ Z'}
    (hg : g = t ≫ v ≫ E₁.hom) (ht : t.left = U.hom)
    (p : B ⟶ Z.left) (hv : v.left = p)
    (κ : B ⟶ B') (L : U.left ⟶ U'.left) (Q : Z'.left ⟶ Y.left)
    (hL : L ≫ U'.hom = U.hom ≫ κ)
    (hS : κ ≫ s ≫ f.left = p ≫ E₀.hom.left ≫ Q) :
    L ≫ a.left = g.left ≫ Q := by
  subst a g E₁
  change L ≫ ((U'.hom ≫ s) ≫ f.left) =
    (t.left ≫ v.left ≫ E₀.hom.left) ≫ Q
  simp only [Category.assoc]
  rw [← Category.assoc L U'.hom (s ≫ f.left), hL, Category.assoc, hS, ht, hv]

end FrobeniusSplitting
