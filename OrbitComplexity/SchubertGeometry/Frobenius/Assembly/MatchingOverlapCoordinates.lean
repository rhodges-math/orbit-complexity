import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Scalar coordinates on overlaps of matching charts

For affine open charts in a smooth separated model, the prescribed scalar
comparison on their overlap is injective on global functions.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
open private common_field_coordinates from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover

/-- A prescribed scalar model of a chart overlap has flat, injective tensor coordinates. -/
theorem matchingOverlap_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y A B PK : Scheme.{u}} [Y.IsSeparated] [IsAffine A] [IsAffine B]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (f : A ⟶ Y) (g : B ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (t : PK ⟶ Spec (.of K)) (q : PK ⟶ pullback f g)
    (h : IsPullback q t (pullback.fst f g ≫ f ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    let : Algebra R Γ(pullback f g, ⊤) :=
      ((pullback.fst f g ≫ f ≫ base).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    let : Algebra K Γ(PK, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    IsAffine (pullback f g) ∧ Module.Flat R Γ(pullback f g, ⊤) ∧
      Function.Injective q.appTop.hom ∧
      ∃ e : K ⊗[R] Γ(pullback f g, ⊤) ≃ₐ[K] Γ(PK, ⊤),
        (∀ k, e (k ⊗ₜ[R] (1 : Γ(pullback f g, ⊤))) =
          algebraMap K Γ(PK, ⊤) k) ∧
        (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
        ∀ k x, e (k ⊗ₜ[R] x) = algebraMap K Γ(PK, ⊤) k * q.appTop.hom x := by
  let : IsAffine (pullback f g) := affine_fibre_product f g
  let : Smooth (pullback.fst f g ≫ f ≫ base) := inferInstance
  exact ⟨inferInstance, common_field_coordinates hR (pullback.fst f g ≫ f ≫ base) t q h⟩

end SchubertGeometry
