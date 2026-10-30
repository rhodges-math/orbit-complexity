import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.SchubertGeometry.Normality.InjectiveImageFamily
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Data.Fintype.Option

/-! # Retained endpoint maps into the same source-coordinate products

The input models and their original generic comparisons are fixed. The
component maps are retained after one coefficient enlargement. Their
product maps then acquire simultaneous retractions without replacing
the chosen target or source-coordinate models.
-/

open CategoryTheory
open scoped TensorProduct

open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u v

/-- A finite product of finitely generated commutative algebras is finitely generated. -/
theorem finiteType_pi (K : Type u) [CommRing K] (I : Type v) [Finite I] :
    ∀ (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
      [∀ i, Algebra.FiniteType K (B i)], Algebra.FiniteType K (∀ i, B i) := by
  classical
  refine Finite.induction_empty_option
    (P := fun I ↦ ∀ (B : I → Type u) [∀ i, CommRing (B i)]
      [∀ i, Algebra K (B i)] [∀ i, Algebra.FiniteType K (B i)],
        Algebra.FiniteType K (∀ i, B i)) ?_ ?_ ?_ I
  · intro I J e ih B _ _ _
    have : Algebra.FiniteType K (∀ i, B (e i)) := ih (fun i ↦ B (e i))
    exact Algebra.FiniteType.equiv inferInstance (AlgEquiv.piCongrLeft K B e)
  · intro B _ _ _
    infer_instance
  · intro I _ ih B _ _ _
    have : Algebra.FiniteType K (∀ i, B (some i)) := ih (fun i ↦ B (some i))
    let e : (∀ i, B i) ≃ₐ[K] (B none × ∀ i, B (some i)) :=
      { RingEquiv.piOptionEquivProd with commutes' _ := rfl }
    exact Algebra.FiniteType.equiv inferInstance e.symm

private theorem cancel_one {S R K M : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] (x : R ⊗[S] M) :
    Algebra.TensorProduct.cancelBaseChange S R K K M ((1 : K) ⊗ₜ[R] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      simp only [Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.smul_def, mul_one]
      rfl
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

private theorem square_of_pure_one {R K M N A B : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R M] [Algebra R N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (g : M →ₐ[R] N) (f : A →ₐ[K] B)
    (h : ∀ x, eN ((1 : K) ⊗ₜ[R] g x) = f (eM ((1 : K) ⊗ₜ[R] x))) :
    eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K g) =
      f.comp eM.toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul k x =>
      change eN (k ⊗ₜ[R] g x) = f (eM (k ⊗ₜ[R] x))
      calc
        _ = k • eN ((1 : K) ⊗ₜ[R] g x) := by
          rw [← map_smul]
          congr 1
          simp [Algebra.smul_def]
        _ = k • f (eM ((1 : K) ⊗ₜ[R] x)) := congrArg (k • ·) (h x)
        _ = f (eM (k ⊗ₜ[R] x)) := by
          rw [← map_smul, ← map_smul]
          congr 1
          simp [Algebra.smul_def]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem injective_of_square {K M N A B : Type u}
    [CommRing K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra K M] [Algebra K N] [Algebra K A] [Algebra K B]
    (eM : M ≃ₐ[K] A) (eN : N ≃ₐ[K] B) (g : M →ₐ[K] N) (f : A →ₐ[K] B)
    (h : eN.toAlgHom.comp g = f.comp eM.toAlgHom) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply eM.injective
  apply hf
  exact (AlgHom.congr_fun h x).symm.trans
    ((congrArg (fun z => eN z) hxy).trans (AlgHom.congr_fun h y))

end
end SchubertGeometry
