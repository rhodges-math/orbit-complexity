import OrbitComplexity.FrobeniusSplitting.Normality.Images.ImageFibreKernel
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # The endpoint image ideal in every coefficient fibre

The sum quotient is formed on the original coefficient ring. Its prescribed
scalar-extension isomorphism and the two quotient factors retain the
ideal identity after every later coefficient extension.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

noncomputable section

private theorem tensor_surjective {S R A B : Type*}
    [CommRing S] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := R) R f) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
      obtain ⟨x, rfl⟩ := hf x
      exact ⟨r ⊗ₜ[S] x, rfl⟩
  | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩

private theorem map_kernel_le {S R A B : Type*}
    [CommRing S] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) :
    (RingHom.ker f.toRingHom).map
      (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom ≤
        RingHom.ker (Algebra.TensorProduct.lTensor (S := R) R f).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change (1 : R) ⊗ₜ[S] f x = 0
  have hx₀ : f x = 0 := RingHom.mem_ker.mp hx
  rw [hx₀, TensorProduct.tmul_zero]

/-- The retained endpoint has exactly the sum of the two Schubert image ideals
after every coefficient extension. The original quotient, its scalar-extension
isomorphism, the factor triangles and the endpoint retraction are used
on their original node domains; no flatness or reducedness is required. -/
theorem endpoint_fibre_sum_kernel {S R F A B O M Q P : Type*}
    [CommRing S] [CommRing R] [CommRing F]
    [CommRing A] [CommRing B] [CommRing O] [CommRing M] [CommRing Q] [CommRing P]
    [Algebra S R] [Algebra R F]
    [Algebra S A] [Algebra S B] [Algebra S O] [Algebra S M] [Algebra S Q]
    [Algebra R P]
    (b : A →ₐ[S] B) (o : A →ₐ[S] O) (m : A →ₐ[S] M) (q : A →ₐ[S] Q)
    (hq : Function.Surjective q)
    (hkq : RingHom.ker q.toRingHom =
      RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom)
    (E : R ⊗[S] Q ≃ₐ[R] R ⊗[S] M)
    (hE : E.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R q) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (θ : R ⊗[S] B →ₐ[R] R ⊗[S] M)
    (ω : R ⊗[S] O →ₐ[R] R ⊗[S] M)
    (hθ : θ.comp (Algebra.TensorProduct.lTensor (S := R) R b) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (hω : ω.comp (Algebra.TensorProduct.lTensor (S := R) R o) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (g : R ⊗[S] M →ₐ[R] P) (r : P →ₗ[R] R ⊗[S] M)
    (hr : r.comp g.toLinearMap = LinearMap.id) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F
      (g.comp (Algebra.TensorProduct.lTensor (S := R) R m))).toRingHom =
      RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F
        (Algebra.TensorProduct.lTensor (S := R) R b)).toRingHom ⊔
      RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F
        (Algebra.TensorProduct.lTensor (S := R) R o)).toRingHom := by
  let bR := Algebra.TensorProduct.lTensor (S := R) R b
  let oR := Algebra.TensorProduct.lTensor (S := R) R o
  let mR := Algebra.TensorProduct.lTensor (S := R) R m
  let qR := Algebra.TensorProduct.lTensor (S := R) R q
  have hcomp : E.toAlgHom.comp qR = mR := hE
  have hmRsurj : Function.Surjective mR := by
    intro y
    obtain ⟨z, hz⟩ := E.surjective y
    obtain ⟨x, hx⟩ := tensor_surjective (R := R) q hq z
    exact ⟨x, (AlgHom.congr_fun hcomp x).symm.trans ((congrArg E hx).trans hz)⟩
  have hmRker : RingHom.ker mR.toRingHom =
      (RingHom.ker q.toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom := by
    have hk : RingHom.ker mR.toRingHom = RingHom.ker qR.toRingHom :=
      (congrArg (fun f : R ⊗[S] A →ₐ[R] R ⊗[S] M ↦ RingHom.ker f.toRingHom)
        hcomp).symm.trans (RingHom.ker_comp_of_injective qR.toRingHom E.injective)
    exact hk.trans (Algebra.TensorProduct.lTensor_ker (A := R) (g := q) hq)
  let bF := Algebra.TensorProduct.lTensor (S := F) F bR
  let oF := Algebra.TensorProduct.lTensor (S := F) F oR
  let mF := Algebra.TensorProduct.lTensor (S := F) F mR
  let ιR : A →ₐ[S] R ⊗[S] A := Algebra.TensorProduct.includeRight
  let ιF : R ⊗[S] A →ₐ[R] F ⊗[R] (R ⊗[S] A) :=
    Algebra.TensorProduct.includeRight
  have hmFker : RingHom.ker mF.toRingHom =
      (RingHom.ker mR.toRingHom).map ιF.toRingHom :=
    Algebra.TensorProduct.lTensor_ker (A := F) (g := mR) hmRsurj
  have hsum : (RingHom.ker mR.toRingHom).map ιF.toRingHom =
      ((RingHom.ker b.toRingHom).map ιR.toRingHom).map ιF.toRingHom ⊔
      ((RingHom.ker o.toRingHom).map ιR.toRingHom).map ιF.toRingHom := by
    calc
      _ = ((RingHom.ker q.toRingHom).map ιR.toRingHom).map ιF.toRingHom :=
        congrArg (fun J : Ideal (R ⊗[S] A) ↦ J.map ιF.toRingHom) hmRker
      _ = ((RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom).map
          ιR.toRingHom).map ιF.toRingHom :=
        congrArg (fun J : Ideal A ↦ (J.map ιR.toRingHom).map ιF.toRingHom) hkq
      _ = _ := by simp only [Ideal.map_sup]
  have hker : RingHom.ker mF.toRingHom =
      RingHom.ker bF.toRingHom ⊔ RingHom.ker oF.toRingHom := by
    apply le_antisymm
    · exact hmFker.le.trans (hsum.le.trans (sup_le
        ((Ideal.map_mono (map_kernel_le (R := R) b)).trans
          ((map_kernel_le (R := F) bR).trans
            (show RingHom.ker bF.toRingHom ≤
              RingHom.ker bF.toRingHom ⊔ RingHom.ker oF.toRingHom from le_sup_left)))
        ((Ideal.map_mono (map_kernel_le (R := R) o)).trans
          ((map_kernel_le (R := F) oR).trans
            (show RingHom.ker oF.toRingHom ≤
              RingHom.ker bF.toRingHom ⊔ RingHom.ker oF.toRingHom from le_sup_right)))))
    · apply sup_le
      · intro x hx
        have hfactor : (Algebra.TensorProduct.lTensor (S := F) F θ).comp bF = mF := by
          change (Algebra.TensorProduct.map (AlgHom.id F F) θ).comp
            (Algebra.TensorProduct.map (AlgHom.id F F) bR) = _
          rw [← Algebra.TensorProduct.map_id_comp, hθ]
        change mF x = 0
        have hx₀ : bF x = 0 := RingHom.mem_ker.mp hx
        exact (AlgHom.congr_fun hfactor x).symm.trans
          ((congrArg (Algebra.TensorProduct.lTensor (S := F) F θ) hx₀).trans (map_zero _))
      · intro x hx
        have hfactor : (Algebra.TensorProduct.lTensor (S := F) F ω).comp oF = mF := by
          change (Algebra.TensorProduct.map (AlgHom.id F F) ω).comp
            (Algebra.TensorProduct.map (AlgHom.id F F) oR) = _
          rw [← Algebra.TensorProduct.map_id_comp, hω]
        change mF x = 0
        have hx₀ : oF x = 0 := RingHom.mem_ker.mp hx
        exact (AlgHom.congr_fun hfactor x).symm.trans
          ((congrArg (Algebra.TensorProduct.lTensor (S := F) F ω) hx₀).trans (map_zero _))
  have hrF : (r.baseChange F).comp (g.toLinearMap.baseChange F) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  have hginj : Function.Injective (Algebra.TensorProduct.lTensor (S := F) F g) :=
    (show Function.LeftInverse (r.baseChange F)
      (Algebra.TensorProduct.lTensor (S := F) F g) from
        fun x ↦ LinearMap.congr_fun hrF x).injective
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id F F) (g.comp mR)).toRingHom = _
  rw [Algebra.TensorProduct.map_id_comp]
  exact (RingHom.ker_comp_of_injective mF.toRingHom hginj).trans hker

end
end FrobeniusSplitting
