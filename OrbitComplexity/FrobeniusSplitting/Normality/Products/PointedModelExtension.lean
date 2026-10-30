import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageGraphs
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImageRanges

/-! # Arithmetic models retaining a point

A finite coefficient graph retains an algebra together with its base-valued
point. The base node is the coefficient ring itself, so the retained point is
an section after scalar extension.
-/

open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u

/-- A smooth model and a generic algebra-valued point admit a smooth coefficient
model with the same point and its exact scalar-extension equation. -/
theorem exists_pointed_model_extension {K B : Type u}
    [CommRing K] [CommRing B] [Algebra K B]
    (S : Subalgebra ℤ K) (hS : S.FG) (H : Type u)
    [CommRing H] [Algebra S H] [Algebra.Smooth S H]
    (e : K ⊗[S] H ≃ₐ[K] B) (epsilon : B →ₐ[K] K) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (H0 : Type u) (_ : CommRing H0) (_ : Algebra R H0)
        (eH : K ⊗[R] H0 ≃ₐ[K] B) (epsilon0 : H0 →ₐ[R] R),
        R.FG ∧ Algebra.Smooth R H0 ∧
        ∀ (k : K) (h : H0),
          epsilon (eH (k ⊗ₜ[R] h)) = k * algebraMap R K (epsilon0 h) := by
  classical
  let initial : Bool → Type u
    | false => S
    | true => H
  let generic : Bool → Type u
    | false => K
    | true => B
  let (b : Bool) : CommRing (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  let (b : Bool) : CommRing (generic b) := by
    cases b <;> dsimp only [generic] <;> infer_instance
  let (b : Bool) : Algebra S (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  let (b : Bool) : Algebra K (generic b) := by
    cases b <;> dsimp only [generic] <;> infer_instance
  have (b : Bool) : Algebra.FinitePresentation S (initial b) := by
    cases b <;> dsimp only [initial] <;> infer_instance
  let comparison : ∀ b, K ⊗[S] initial b ≃ₐ[K] generic b
    | false => Algebra.TensorProduct.rid S K K
    | true => e
  have hsmooth : ∀ b ∈ ({true} : Set Bool), Algebra.Smooth S (initial b) := by
    intro b hb
    have heq : b = true := hb
    subst b
    exact inferInstanceAs (Algebra.Smooth S H)
  obtain ⟨R, hSR, models, eqv, hR, hmodels, hfp, hsm, heval, hmaps, helts⟩ :=
    exists_scalar_image_graph S hS initial generic comparison {true} hsmooth
      (fun _ : Unit => true) (fun _ => false) (fun _ => epsilon)
      (fun _ => Empty) (fun _ z => nomatch z)
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have hbase : models false = (⊥ : Subalgebra R K) := by
    rw [hmodels false, scalarImage_range]
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨s, rfl⟩
      change ∃ r : R, algebraMap R K r =
        (Algebra.TensorProduct.rid S K K) ((1 : K) ⊗ₜ[S] s)
      refine ⟨algebraMap S R s, ?_⟩
      simp only [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
      exact (IsScalarTower.algebraMap_apply S R K s).symm
    · exact bot_le
  let Q : models false ≃ₐ[R] R :=
    (Subalgebra.equivOfEq _ _ hbase).trans
      (Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K))
  have hQ (y : models false) : algebraMap R K (Q y) = y.val := by
    have hy : Q.symm (Q y) = algebraMap R (models false) (Q y) := by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using Q.symm.commutes (Q y)
    rw [Q.symm_apply_apply] at hy
    exact (congrArg Subtype.val hy).symm
  let epsilonModel : models true →ₐ[R] models false :=
    ((epsilon.restrictScalars R).comp (models true).val).codRestrict (models false)
      (fun x => hmaps () x.property)
  let epsilon0 : models true →ₐ[R] R := Q.toAlgHom.comp epsilonModel
  have hE (h : models true) : algebraMap R K (epsilon0 h) = epsilon h.val :=
    hQ (epsilonModel h)
  refine ⟨R, hSR, models true, inferInstance, inferInstance, eqv true, epsilon0,
    hR, hsm true (Set.mem_singleton true), ?_⟩
  intro k h
  calc
    epsilon (eqv true (k ⊗ₜ[R] h)) =
        epsilon (algebraMap K B k * h.val) := congrArg epsilon (heval true k h)
    _ = k * epsilon h.val := by
      rw [map_mul, epsilon.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    _ = k * algebraMap R K (epsilon0 h) := congrArg (k * ·) (hE h).symm

end
end FrobeniusSplitting
