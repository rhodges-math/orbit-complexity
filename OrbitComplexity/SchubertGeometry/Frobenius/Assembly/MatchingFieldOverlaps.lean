import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOverlapCoordinates
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.ScalarOverlapSquares
import Batteries.Tactic.Lint

/-!
# Field comparisons on matching-chart overlaps

Individual Cartesian chart comparisons construct the scalar map on the
pairwise overlap and its flat, injective coordinate comparison.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

/-- The chart squares construct the field-overlap map and all its tensor coordinates. -/
theorem matchingOverlap_field_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y Z A B AK BK : Scheme.{u}} [Y.IsSeparated] [IsAffine A] [IsAffine B]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (f : A ⟶ Y) (g : B ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (fK : AK ⟶ Z) (gK : BK ⟶ Z) (u : AK ⟶ A) (v : BK ⟶ B) (z : Z ⟶ Y)
    (hu : u ≫ f = fK ≫ z) (hv : v ≫ g = gK ≫ z)
    (tA : AK ⟶ Spec (.of K))
    (hA : IsPullback u tA (f ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hB : IsPullback v gK g z) :
    let q := pullback.map fK gK f g u v z hu.symm hv.symm
    let t := pullback.fst fK gK ≫ tA
    let : Algebra R Γ(pullback f g, ⊤) :=
      ((pullback.fst f g ≫ f ≫ base).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    let : Algebra K Γ(pullback fK gK, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    IsPullback q t (pullback.fst f g ≫ f ≫ base)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsAffine (pullback f g) ∧ Module.Flat R Γ(pullback f g, ⊤) ∧
        Function.Injective q.appTop.hom ∧
        ∃ e : K ⊗[R] Γ(pullback f g, ⊤) ≃ₐ[K] Γ(pullback fK gK, ⊤),
          (∀ k, e (k ⊗ₜ[R] (1 : Γ(pullback f g, ⊤))) =
            algebraMap K Γ(pullback fK gK, ⊤) k) ∧
          (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
          ∀ k x, e (k ⊗ₜ[R] x) =
            algebraMap K Γ(pullback fK gK, ⊤) k * q.appTop.hom x := by
  let q := pullback.map fK gK f g u v z hu.symm hv.symm
  let t := pullback.fst fK gK ≫ tA
  have hq : IsPullback q t (pullback.fst f g ≫ f ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    exact scalarOverlap_isPullback f g fK gK u v z hu hv (f ≫ base) tA
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) hA hB
  exact ⟨hq, matchingOverlap_coordinates hR base f g t q hq⟩

end SchubertGeometry
