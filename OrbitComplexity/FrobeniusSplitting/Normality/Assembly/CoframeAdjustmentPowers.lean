import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframe powers over one coefficient extension

If the scalar coframe ratios are the powers of their degree-one ratios, the
retained degree-one unit family supplies every degree over the same ring.
The units in degree n are the n-th powers of that single family.
-/

set_option autoImplicit false

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory
open FrobeniusSplitting.CharacterLine
open scoped TensorProduct

namespace FrobeniusSplitting.RetainedCharacter

open private scalarMap adjustedFamilyData adjustments_of_units from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

/-- One retained unit family gives all powers of a coframe comparison over
the same coefficient extension, with the chosen unit powers exhibited. -/
theorem coframeAdjustments_powers
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {I : Type v} (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (f : ∀ i, M i →+* A i)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : ℕ → Y.Modules)
    (j : ∀ i, Spec (.of (M i)) ⟶ Y)
    (a : ∀ i, Spec (.of (A i)) ⟶ YK)
    (hscalar : ∀ i, Spec.map (CommRingCat.ofHom (f i)) ≫ j i = a i ≫ q)
    (E : ∀ n i, (Scheme.Modules.pullback (j i)).obj (L n) ≅
      SheafOfModules.unit (Spec (.of (M i))).ringCatSheaf)
    (F : ∀ n i, (Scheme.Modules.pullback (a i)).obj
      ((Scheme.Modules.pullback q).obj (L n)) ≅
        SheafOfModules.unit (Spec (.of (A i))).ringCatSheaf)
    (he : ∀ i x, e i ((1 : K) ⊗ₜ[S] x) = f i x)
    (hdata : adjustedFamilyData (R := R) M A e f q (L 1) j a hscalar (E 1) (F 1))
    (hratio : ∀ n i, affineCoframeUnit (A i)
      (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (f i)))
        (hscalar i) (L n) (E n i)) (F n i) =
      (affineCoframeUnit (A i)
        (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (f i)))
          (hscalar i) (L 1) (E 1 i)) (F 1 i)) ^ n) :
    ∃ d : ∀ i, (R ⊗[S] M i)ˣ,
      (∀ n i, scalarMap (R := R) (e i) ((d i : R ⊗[S] M i) ^ n) =
        (affineCoframeUnit (A i)
          (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (f i)))
            (hscalar i) (L n) (E n i)) (F n i) : A i)) ∧
      ∀ n, adjustedFamilyData (R := R) M A e f q (L n) j a hscalar (E n) (F n) := by
  obtain ⟨d, hd, _, _⟩ := hdata
  let ratio : ∀ n i, (A i)ˣ := fun n i => affineCoframeUnit (A i)
    (squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom (f i)))
      (hscalar i) (L n) (E n i)) (F n i)
  have hdn : ∀ n i, scalarMap (R := R) (e i) ((d i : R ⊗[S] M i) ^ n) =
      (ratio n i : A i) := by
    intro n i
    calc
      _ = (scalarMap (R := R) (e i) (d i : R ⊗[S] M i)) ^ n := map_pow _ _ _
      _ = (ratio 1 i : A i) ^ n := congrArg (fun x : A i => x ^ n) (hd i)
      _ = _ := congrArg (fun x : (A i)ˣ => (x : A i)) (hratio n i).symm
  refine ⟨d, hdn, ?_⟩
  intro n
  apply adjustments_of_units (R := R) M A e f q (L n) j a hscalar (E n) (F n)
    he (fun i => d i ^ n)
  · intro i
    exact hdn n i
  · intro i k
    change scalarMap (R := R) (e i) (((d i : R ⊗[S] M i) ^ n) ^ k) =
      (ratio n i : A i) ^ k
    rw [map_pow]
    exact congrArg (fun x : A i => x ^ k) (hdn n i)

end FrobeniusSplitting.RetainedCharacter
