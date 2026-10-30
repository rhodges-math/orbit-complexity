import OrbitComplexity.FrobeniusSplitting.Normality.Images.RichardsonFibreIdeal
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Endpoint fibre kernels on the prescribed quotient charts

The target chart isomorphisms preserve all ambient-map squares. The endpoint
retraction is transported from the specified chosen target chart, while the source
coordinate algebra is left unchanged. This gives the specialized kernel sum
on the chosen charts after every coefficient extension.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

noncomputable section

universe u

/-- A retraction of the prescribed endpoint map transfers through its target
chart isomorphism, keeping the original source-coordinate algebra. -/
theorem endpoint_retraction_transport {R M M' P : Type u}
    [CommRing R] [CommRing M] [CommRing M'] [CommRing P]
    [Algebra R M] [Algebra R M'] [Algebra R P]
    (e : M ≃ₐ[R] M') (g : M' →ₐ[R] P) (r : P →ₗ[R] M')
    (hr : r.comp g.toLinearMap = LinearMap.id) :
    (e.symm.toLinearMap.comp r).comp (g.comp e.toAlgHom).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  change e.symm (r (g (e x))) = x
  have hx : r (g (e x)) = e x := LinearMap.congr_fun hr (e x)
  rw [hx, e.symm_apply_apply]

private theorem kernel_map_of_square {R A B A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    (f : A →ₐ[R] B) (f' : A' →ₐ[R] B')
    (h : eB.toAlgHom.comp f = f'.comp eA.toAlgHom) :
    (RingHom.ker f.toRingHom).map eA.toRingHom = RingHom.ker f'.toRingHom := by
  have hc : RingHom.ker f.toRingHom =
      (RingHom.ker f'.toRingHom).comap eA.toRingHom := by
    calc
      _ = RingHom.ker (eB.toAlgHom.comp f).toRingHom :=
        (RingHom.ker_comp_of_injective f.toRingHom eB.injective).symm
      _ = RingHom.ker (f'.comp eA.toAlgHom).toRingHom :=
        congrArg (fun z : A →ₐ[R] B' ↦ RingHom.ker z.toRingHom) h
      _ = _ := (RingHom.comap_ker f'.toRingHom eA.toRingHom).symm
  rw [hc]
  exact Ideal.map_comap_of_surjective eA.toRingHom eA.surjective _

private theorem tensor_equiv_square {R F A B A' B' : Type u}
    [CommRing R] [CommRing F] [CommRing A] [CommRing B]
    [CommRing A'] [CommRing B']
    [Algebra R F] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    (f : A →ₐ[R] B) (f' : A' →ₐ[R] B')
    (h : eB.toAlgHom.comp f = f'.comp eA.toAlgHom) :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eB).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := F) F f) =
      (Algebra.TensorProduct.lTensor (S := F) F f').comp
        (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eA).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c a =>
      change c ⊗ₜ[R] eB (f a) = c ⊗ₜ[R] f' (eA a)
      exact congrArg (fun b : B' ↦ c ⊗ₜ[R] b) (AlgHom.congr_fun h a)
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem kernel_sum_transport {R A B O P A' B' O' P' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing O] [CommRing P]
    [CommRing A'] [CommRing B'] [CommRing O'] [CommRing P']
    [Algebra R A] [Algebra R B] [Algebra R O] [Algebra R P]
    [Algebra R A'] [Algebra R B'] [Algebra R O'] [Algebra R P']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') (eO : O ≃ₐ[R] O') (eP : P ≃ₐ[R] P')
    (b : A →ₐ[R] B) (o : A →ₐ[R] O) (f : A →ₐ[R] P)
    (b' : A' →ₐ[R] B') (o' : A' →ₐ[R] O') (f' : A' →ₐ[R] P')
    (hb : eB.toAlgHom.comp b = b'.comp eA.toAlgHom)
    (ho : eO.toAlgHom.comp o = o'.comp eA.toAlgHom)
    (hf : eP.toAlgHom.comp f = f'.comp eA.toAlgHom)
    (h : RingHom.ker f.toRingHom = RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom) :
    RingHom.ker f'.toRingHom = RingHom.ker b'.toRingHom ⊔ RingHom.ker o'.toRingHom := by
  calc
    _ = (RingHom.ker f.toRingHom).map eA.toRingHom :=
      (kernel_map_of_square eA eP f f' hf).symm
    _ = (RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom).map eA.toRingHom :=
      congrArg (fun I : Ideal A ↦ I.map eA.toRingHom) h
    _ = (RingHom.ker b.toRingHom).map eA.toRingHom ⊔
        (RingHom.ker o.toRingHom).map eA.toRingHom := Ideal.map_sup _ _ _
    _ = _ := congrArg₂ (fun I J : Ideal A' ↦ I ⊔ J)
      (kernel_map_of_square eA eB b b' hb) (kernel_map_of_square eA eO o o' ho)

/-- The retained quotient-factor data give the specialized endpoint kernel sum
on the same chosen ambient, ordinary, opposite and reduced target chart rings.
The retraction belongs to the specified chosen endpoint map and is transported
internally; no specialized ideal identity or source-cover comparison is assumed. -/
theorem endpoint_sum_kernel_transport {S R F A B O M Q A' B' O' M' P : Type u}
    [CommRing S] [CommRing R] [CommRing F]
    [CommRing A] [CommRing B] [CommRing O] [CommRing M] [CommRing Q]
    [CommRing A'] [CommRing B'] [CommRing O'] [CommRing M'] [CommRing P]
    [Algebra S R] [Algebra R F]
    [Algebra S A] [Algebra S B] [Algebra S O] [Algebra S M] [Algebra S Q]
    [Algebra R A'] [Algebra R B'] [Algebra R O'] [Algebra R M'] [Algebra R P]
    (b : A →ₐ[S] B) (o : A →ₐ[S] O) (m : A →ₐ[S] M) (q : A →ₐ[S] Q)
    (hq : Function.Surjective q)
    (hkq : RingHom.ker q.toRingHom = RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom)
    (E : R ⊗[S] Q ≃ₐ[R] R ⊗[S] M)
    (hE : E.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R q) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (θ : R ⊗[S] B →ₐ[R] R ⊗[S] M) (ω : R ⊗[S] O →ₐ[R] R ⊗[S] M)
    (hθ : θ.comp (Algebra.TensorProduct.lTensor (S := R) R b) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (hω : ω.comp (Algebra.TensorProduct.lTensor (S := R) R o) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (eA : R ⊗[S] A ≃ₐ[R] A') (eB : R ⊗[S] B ≃ₐ[R] B')
    (eO : R ⊗[S] O ≃ₐ[R] O') (eM : R ⊗[S] M ≃ₐ[R] M')
    (b' : A' →ₐ[R] B') (o' : A' →ₐ[R] O') (m' : A' →ₐ[R] M')
    (hb : eB.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R b) =
      b'.comp eA.toAlgHom)
    (ho : eO.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R o) =
      o'.comp eA.toAlgHom)
    (hm : eM.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R m) =
      m'.comp eA.toAlgHom)
    (g : M' →ₐ[R] P) (r : P →ₗ[R] M')
    (hr : r.comp g.toLinearMap = LinearMap.id) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F (g.comp m')).toRingHom =
      RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F b').toRingHom ⊔
      RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F o').toRingHom := by
  let bR := Algebra.TensorProduct.lTensor (S := R) R b
  let oR := Algebra.TensorProduct.lTensor (S := R) R o
  let mR := Algebra.TensorProduct.lTensor (S := R) R m
  let g₀ : R ⊗[S] M →ₐ[R] P := g.comp eM.toAlgHom
  let r₀ : P →ₗ[R] R ⊗[S] M := eM.symm.toLinearMap.comp r
  have hr₀ : r₀.comp g₀.toLinearMap = LinearMap.id :=
    endpoint_retraction_transport eM g r hr
  have hk := endpoint_fibre_sum_kernel (F := F) b o m q hq hkq E hE θ ω hθ hω g₀ r₀ hr₀
  have hendpoint : (AlgEquiv.refl : P ≃ₐ[R] P).toAlgHom.comp (g₀.comp mR) =
      (g.comp m').comp eA.toAlgHom := by
    apply AlgHom.ext
    intro x
    change g (eM (mR x)) = g (m' (eA x))
    exact congrArg g (AlgHom.congr_fun hm x)
  let eAF := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eA
  let eBF := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eB
  let eOF := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) eO
  let ePF := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F)
    (AlgEquiv.refl : P ≃ₐ[R] P)
  exact kernel_sum_transport eAF eBF eOF ePF
    (Algebra.TensorProduct.lTensor (S := F) F bR)
    (Algebra.TensorProduct.lTensor (S := F) F oR)
    (Algebra.TensorProduct.lTensor (S := F) F (g₀.comp mR))
    (Algebra.TensorProduct.lTensor (S := F) F b')
    (Algebra.TensorProduct.lTensor (S := F) F o')
    (Algebra.TensorProduct.lTensor (S := F) F (g.comp m'))
    (tensor_equiv_square eA eB bR b' hb)
    (tensor_equiv_square eA eO oR o' ho)
    (tensor_equiv_square eA (AlgEquiv.refl : P ≃ₐ[R] P)
      (g₀.comp mR) (g.comp m') hendpoint) hk

end
end FrobeniusSplitting
