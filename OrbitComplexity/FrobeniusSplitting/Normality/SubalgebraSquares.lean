import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ImageSquares

/-!
# Subalgebra Squares

Flat subalgebra models preserve generic pushouts when their images generate.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FrobeniusSplitting

universe u

set_option maxHeartbeats 400000 in
/-- Flat subalgebra models of an affine pushout form a pushout when their images generate. -/
theorem isPushout_of_subalgebra_models {K A B C D : Type u}
    [CommRing K] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra K D]
    (R : Subalgebra ℤ K) (f : A →ₐ[K] B) (g : A →ₐ[K] C)
    (p : B →ₐ[K] D) (q : C →ₐ[K] D)
    (hpush : IsPushout (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)
      (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom))
    (M : Subalgebra R A) (N : Subalgebra R B) (P : Subalgebra R C) (Q : Subalgebra R D)
    (f₀ : M →ₐ[R] N) (g₀ : M →ₐ[R] P) (p₀ : N →ₐ[R] Q) (q₀ : P →ₐ[R] Q)
    (hf : ∀ x, (f₀ x).val = f x.val) (hg : ∀ x, (g₀ x).val = g x.val)
    (hp : ∀ x, (p₀ x).val = p x.val) (hq : ∀ x, (q₀ x).val = q x.val)
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (eP : K ⊗[R] P ≃ₐ[K] C)
    (hM : ∀ x, eM ((1 : K) ⊗ₜ[R] x) = x.val)
    (hN : ∀ x, eN ((1 : K) ⊗ₜ[R] x) = x.val)
    (hP : ∀ x, eP ((1 : K) ⊗ₜ[R] x) = x.val)
    (hfFlat : f₀.toRingHom.Flat) (hgFlat : g₀.toRingHom.Flat)
    (hgen : p₀.range ⊔ q₀.range = ⊤) :
    IsPushout (CommRingCat.ofHom f₀.toRingHom) (CommRingCat.ofHom g₀.toRingHom)
      (CommRingCat.ofHom p₀.toRingHom) (CommRingCat.ofHom q₀.toRingHom) := by
  have hcomm : p.comp f = q.comp g := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun t ↦ t.hom a) hpush.w
  have hcomm₀ : p₀.comp f₀ = q₀.comp g₀ := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    calc
      (p₀ (f₀ x)).val = p (f x.val) := (hp (f₀ x)).trans (congrArg p (hf x))
      _ = q (g x.val) := AlgHom.congr_fun hcomm x.val
      _ = (q₀ (g₀ x)).val := ((hq (g₀ x)).trans (congrArg q (hg x))).symm
  let : Algebra A B := f.toAlgebra
  let : Algebra A C := g.toAlgebra
  let : Algebra B D := p.toAlgebra
  let : Algebra C D := q.toAlgebra
  let : Algebra A D := (p.comp f).toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a ↦
    AlgHom.congr_fun hcomm a
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.mp hpush
  let eD : B ⊗[A] C ≃ₐ[A] D := (Algebra.IsPushout.equiv A B C D).restrictScalars A
  let : Algebra M N := f₀.toAlgebra
  let : Algebra M P := g₀.toAlgebra
  let : Algebra M Q := (p₀.comp f₀).toAlgebra
  have : IsScalarTower M N B := IsScalarTower.of_algebraMap_eq fun x ↦ (hf x).symm
  have : IsScalarTower M P C := IsScalarTower.of_algebraMap_eq fun x ↦ (hg x).symm
  have : Module.Flat M N := hfFlat
  have : Module.Flat M P := hgFlat
  let pM : N →ₐ[M] Q :=
    { p₀.toRingHom with commutes' := fun _ ↦ rfl }
  let qM : P →ₐ[M] Q :=
    { q₀.toRingHom with commutes' := fun x ↦ (AlgHom.congr_fun hcomm₀ x).symm }
  let ι : Q →ₐ[M] D :=
    { Q.val.toRingHom with
      commutes' := fun x ↦ (hp (f₀ x)).trans (congrArg p (hf x)) }
  let eB := relativeScalarEquiv eM eN hM hN
  let eC := relativeScalarEquiv eM eP hM hP
  let s := IsScalarTower.toAlgHom M N B
  let t := IsScalarTower.toAlgHom M P C
  let v := IsScalarTower.toAlgHom A B D
  let w := IsScalarTower.toAlgHom A C D
  have hgenM : pM.range ⊔ qM.range = ⊤ := by
    have hle : p₀.range ⊔ q₀.range ≤ (pM.range ⊔ qM.range).restrictScalars R := by
      apply sup_le
      · intro z hz
        obtain ⟨x, hx⟩ := hz
        have hmem : pM x ∈ pM.range ⊔ qM.range :=
          Algebra.mem_sup_left (AlgHom.mem_range_self pM x)
        exact hx ▸ hmem
      · intro z hz
        obtain ⟨x, hx⟩ := hz
        have hmem : qM x ∈ pM.range ⊔ qM.range :=
          Algebra.mem_sup_right (AlgHom.mem_range_self qM x)
        exact hx ▸ hmem
    apply le_antisymm le_top
    intro z _
    apply hle
    rw [hgen]
    trivial
  exact isPushout_of_relative_images pM qM ι eB eC eD s t v w
    (relativeScalarEquiv_tmul eM eN hM hN) (relativeScalarEquiv_tmul eM eP hM hP)
    (fun b c ↦ Algebra.IsPushout.equiv_tmul A B C D b c) hp hq
    Subtype.val_injective hgenM

end FrobeniusSplitting
