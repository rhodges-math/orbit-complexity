import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps
import Batteries.Tactic.Lint

/-! # Localization comparisons after scalar extension

A localization isomorphism retaining the source algebra map induces the
corresponding localization isomorphism over every coefficient algebra.
All comparisons are whole ring maps.
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FrobeniusSplitting

universe u

/-- Scalar extension preserves a localization isomorphism and its source-map
square. The two resulting rings are the principal localizations of the exact
scalar extensions of the source and target algebras. -/
theorem localization_baseChange_equiv {R A B C D L : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing L]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R L]
    [Algebra A C] [Algebra B D] [IsScalarTower R A C] [IsScalarTower R B D]
    (f : A →ₐ[R] B) (d : A) [IsLocalization.Away d C]
    [IsLocalization.Away (f d) D] (E : C ≃+* D)
    (hE : E.toRingHom.comp (algebraMap A C) =
      (algebraMap B D).comp f.toRingHom) :
    ∃ EL : Localization.Away ((1 : L) ⊗ₜ[R] d) ≃+*
        Localization.Away ((1 : L) ⊗ₜ[R] f d),
      EL.toRingHom.comp (algebraMap (L ⊗[R] A)
        (Localization.Away ((1 : L) ⊗ₜ[R] d))) =
      (algebraMap (L ⊗[R] B) (Localization.Away ((1 : L) ⊗ₜ[R] f d))).comp
        (Algebra.TensorProduct.lTensor (S := L) L f).toRingHom := by
  have hR (r : R) : E (algebraMap R C r) = algebraMap R D r := by
    rw [IsScalarTower.algebraMap_apply R A C,
      IsScalarTower.algebraMap_apply R B D]
    exact (DFunLike.congr_fun hE (algebraMap R A r)).trans
      (congrArg (algebraMap B D) (f.commutes r))
  let ER : C ≃ₐ[R] D := AlgEquiv.ofRingEquiv (f := E) hR
  let EA : L ⊗[R] C ≃ₐ[L] Localization.Away ((1 : L) ⊗ₜ[R] d) :=
    IsLocalization.Away.tensorProductEquivTMulRight R L d C
  let EB : L ⊗[R] D ≃ₐ[L] Localization.Away ((1 : L) ⊗ₜ[R] f d) :=
    IsLocalization.Away.tensorProductEquivTMulRight R L (f d) D
  let ET : L ⊗[R] C ≃ₐ[L] L ⊗[R] D :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) ER
  let EL := EA.symm.trans (ET.trans EB)
  refine ⟨EL.toRingEquiv, ?_⟩
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul l a =>
    have ha : E (algebraMap A C a) = algebraMap B D (f a) :=
      DFunLike.congr_fun hE a
    have hinv : EA.symm (algebraMap (L ⊗[R] A)
          (Localization.Away ((1 : L) ⊗ₜ[R] d)) (l ⊗ₜ[R] a)) =
        l ⊗ₜ[R] algebraMap A C a := by
      apply EA.injective
      simpa only [AlgEquiv.apply_symm_apply] using
        (IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := L) (A := A)
          (g := d) (B := C) (x := l) (a := a)).symm
    have hET : ET (l ⊗ₜ[R] algebraMap A C a) =
        l ⊗ₜ[R] algebraMap B D (f a) := by
      change (Algebra.TensorProduct.map (AlgEquiv.refl : L ≃ₐ[L] L).toAlgHom ER.toAlgHom)
        (l ⊗ₜ[R] algebraMap A C a) = _
      rw [Algebra.TensorProduct.map_tmul]
      change l ⊗ₜ[R] E (algebraMap A C a) = _
      rw [ha]
    change EB (ET (EA.symm (algebraMap (L ⊗[R] A)
        (Localization.Away ((1 : L) ⊗ₜ[R] d)) (l ⊗ₜ[R] a)))) =
      algebraMap (L ⊗[R] B) (Localization.Away ((1 : L) ⊗ₜ[R] f d))
        ((Algebra.TensorProduct.lTensor (S := L) L f) (l ⊗ₜ[R] a))
    rw [hinv, hET]
    simpa only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply] using
      IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := L) (A := B)
        (g := f d) (B := D) (x := l) (a := f a)
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A regular localization isomorphism gives an injective algebra map to the source
localization. -/
theorem away_inverse {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (d : A) (hd : IsRegular (f d))
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (f d))).comp f.toRingHom) :
    ∃ q : B →ₐ[K] Localization.Away d,
      Function.Injective q ∧
      q.comp f = IsScalarTower.toAlgHom K A (Localization.Away d) := by
  let qR : B →+* Localization.Away d := E.symm.toRingHom.comp
    (algebraMap B (Localization.Away (f d)))
  have hqf (a : A) : qR (f a) = algebraMap A (Localization.Away d) a := by
    apply E.injective
    change E (E.symm (algebraMap B (Localization.Away (f d)) (f a))) = _
    rw [E.apply_symm_apply]
    exact (DFunLike.congr_fun hE a).symm
  let q : B →ₐ[K] Localization.Away d :=
    { qR with
      commutes' := fun k => by
        change qR (algebraMap K B k) = algebraMap K (Localization.Away d) k
        rw [← f.commutes k, hqf]
        exact (IsScalarTower.algebraMap_apply K A (Localization.Away d) k).symm }
  have hi : Function.Injective (algebraMap B (Localization.Away (f d))) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers (f d)) (S := Localization.Away (f d))
      (fun z hz => by obtain ⟨n, rfl⟩ := hz; exact hd.pow n)
  refine ⟨q, E.symm.injective.comp hi, ?_⟩
  exact AlgHom.ext hqf

/-- An injective map into the source localization makes the localization map bijective. -/
theorem away_bijective_of_injection {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (f : A →+* B) (d : A) [IsLocalization.Away d C]
    (q : B →+* C) (hq : Function.Injective q)
    (hsquare : q.comp f = algebraMap A C) :
    Function.Bijective (Localization.awayMap f d) := by
  have hqf (a : A) : q (f a) = algebraMap A C a :=
    DFunLike.congr_fun hsquare a
  constructor
  · apply Localization.awayMap_injective_iff.mpr
    intro a ha
    have hz : algebraMap A C a = algebraMap A C 0 := by
      rw [← hqf a, ha, map_zero, map_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers d)
      C).mp hz
    obtain ⟨n, hn⟩ := c.property
    exact ⟨n, by simpa only [hn, mul_zero] using hc⟩
  · apply Localization.awayMap_surjective_iff.mpr
    intro b
    obtain ⟨a, c, hc⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers d) (q b)
    obtain ⟨n, hn⟩ := c.property
    refine ⟨a, n, hq ?_⟩
    rw [map_mul, map_pow, hqf a, hqf d]
    have hm := IsLocalization.mk'_spec C a c
    rw [hc, ← hn, map_pow] at hm
    exact hm.symm.trans (mul_comm _ _)

/-- Scalar extension commutes with principal localization through a tensor isomorphism. -/
def tensorAwayComparison {R K M A : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra K A]
    (e : K ⊗[R] M ≃ₐ[K] A) (d : M) :
    K ⊗[R] Localization.Away d ≃ₐ[K]
      Localization.Away (e ((1 : K) ⊗ₜ[R] d)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight R K d (Localization.Away d)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : K) ⊗ₜ[R] d))
      (T := Submonoid.powers (e ((1 : K) ⊗ₜ[R] d)))
      (Localization.Away ((1 : K) ⊗ₜ[R] d))
      (Localization.Away (e ((1 : K) ⊗ₜ[R] d))) e
      (by simp only [Submonoid.map_powers]))

/-- The scalar localization isomorphism evaluates pure tensors by the tensor isomorphism. -/
theorem tensorAwayComparison_tmul {R K M A : Type u}
    [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra R K] [Algebra R M] [Algebra K A]
    (e : K ⊗[R] M ≃ₐ[K] A) (d m : M) (k : K) :
    tensorAwayComparison e d (k ⊗ₜ[R] algebraMap M (Localization.Away d) m) =
      algebraMap A (Localization.Away (e ((1 : K) ⊗ₜ[R] d))) (e (k ⊗ₜ[R] m)) := by
  simp only [tensorAwayComparison, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq]

end FrobeniusSplitting
