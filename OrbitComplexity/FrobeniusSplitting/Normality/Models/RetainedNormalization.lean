import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.FreePair
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteNormalizationModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.LocalizationFibres
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained localization comparisons

A map from a finite algebra into a principal localization is retained on
prescribed finitely presented models. Flat coefficient models let the
comparison equations be checked in the field extension.
-/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace FrobeniusSplitting
universe u

open private rebased_comparison_square
  from OrbitComplexity.FrobeniusSplitting.Normality.Images.ModelScalarSquares

private theorem retain_element {K M A : Type u}
    [Field K] [CommRing M] [CommRing A]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra.FinitePresentation S M] [Algebra K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (a : A) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ ∃ m : T ⊗[S] M,
        e (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
          (AlgHom.id S M) m) = a := by
  let vars (_ : Unit) := Fin (Algebra.Presentation.ofFinitePresentationVars S M)
  let rels (_ : Unit) := Fin (Algebra.Presentation.ofFinitePresentationRels S M)
  let Q (_ : Unit) : Algebra.Presentation S M (vars ()) (rels ()) :=
    Algebra.Presentation.ofFinitePresentation S M
  obtain ⟨T, hST, _f, hT, _hf, hm⟩ := exists_chosen_graph_elements S hS
    (fun _ : Unit => M) (fun _ : Unit => A) (fun _ => e) vars rels Q
    (fun z : Empty => z.elim) (fun z : Empty => z.elim) (fun z => z.elim)
    (fun _ => Unit) (fun _ _ => a)
  exact ⟨T, hST, hT, hm () ()⟩

private theorem retain_map {K M N A B : Type u}
    [Field K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra S N] [Algebra K A] [Algebra K B]
    [Algebra.FinitePresentation S M] [Algebra.FinitePresentation S N]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (q : A →ₐ[K] B) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ ∃ qT : T ⊗[S] M →ₐ[T] T ⊗[S] N,
        ∀ m,
          eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
            (AlgHom.id S N) (qT m)) =
          q (eM (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
            (AlgHom.id S M) m)) := by
  let models : Bool → Type u := fun b => if b then M else N
  let fibres : Bool → Type u := fun b => if b then A else B
  let (b : Bool) : CommRing (models b) := by cases b <;> dsimp [models] <;> infer_instance
  let (b : Bool) : CommRing (fibres b) := by cases b <;> dsimp [fibres] <;> infer_instance
  let (b : Bool) : Algebra S (models b) := by cases b <;> dsimp [models] <;> infer_instance
  let (b : Bool) : Algebra K (fibres b) := by cases b <;> dsimp [fibres] <;> infer_instance
  let (b : Bool) : Algebra.FinitePresentation S (models b) := by
    cases b <;> dsimp [models] <;> infer_instance
  let e (b : Bool) : K ⊗[S] models b ≃ₐ[K] fibres b := by
    cases b
    · exact eN
    · exact eM
  let vars (b : Bool) := Fin (Algebra.Presentation.ofFinitePresentationVars S (models b))
  let rels (b : Bool) := Fin (Algebra.Presentation.ofFinitePresentationRels S (models b))
  let Q (b : Bool) : Algebra.Presentation S (models b) (vars b) (rels b) :=
    Algebra.Presentation.ofFinitePresentation S (models b)
  let arrow (_ : Unit) : fibres true →ₐ[K] fibres false := q
  obtain ⟨T, hST, qT, hT, hqT, _helts⟩ := exists_chosen_graph_elements S hS
    models fibres e vars rels Q (fun _ : Unit => true) (fun _ => false) arrow
    (fun _ => Empty) (fun _ z => z.elim)
  exact ⟨T, hST, hT, qT (), hqT ()⟩

private theorem tensor_away_square {S T M : Type u}
    [CommRing S] [CommRing T] [CommRing M] [Algebra S T] [Algebra S M] (d : M) :
    (IsLocalization.Away.tensorProductEquivTMulRight S T d
      (Localization.Away d)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := T) T
          (IsScalarTower.toAlgHom S M (Localization.Away d))) =
      IsScalarTower.toAlgHom T (T ⊗[S] M)
        (Localization.Away ((1 : T) ⊗ₜ[S] d)) := by
  apply Algebra.TensorProduct.ext'
  intro t m
  exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := S) (S := T)
    (g := d) (B := Localization.Away d) (x := t) (a := m)

private def awayModelData {R M N : Type u}
    [CommRing R] [CommRing M] [CommRing N] [Algebra R M] [Algebra R N]
    (f : M →ₐ[R] N) (d : M) : Prop :=
  ∃ E : Localization.Away d ≃+* Localization.Away (f d),
    E.toRingHom.comp (algebraMap M (Localization.Away d)) =
      (algebraMap N (Localization.Away (f d))).comp f.toRingHom

private theorem away_packet {S R T K M N A B : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [IsScalarTower R T K]
    [Algebra S M] [Algebra S N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (f : M →ₐ[S] N) (fK : A →ₐ[K] B) (d : M)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp eM.toAlgHom)
    (qK : B →ₐ[K] Localization.Away (modelEval eM d))
    (hqK : Function.Injective qK)
    (hqf : qK.comp fK = IsScalarTower.toAlgHom K A (Localization.Away (modelEval eM d)))
    (qR : R ⊗[S] N →ₐ[R] R ⊗[S] Localization.Away d)
    (hqR : ∀ n,
      tensorAwayComparison eM d
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (Localization.Away d)) (qR n)) =
      qK (eN (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S N) n)))
    [Module.Free T (T ⊗[R] (R ⊗[S] N))]
    [Module.Free T (T ⊗[R] (R ⊗[S] Localization.Away d))]
    (hi : Function.Injective (algebraMap T K)) :
    awayModelData (Algebra.TensorProduct.lTensor (S := T) T f) ((1 : T) ⊗ₜ[S] d) := by
  let C := Localization.Away d
  let eC := tensorAwayComparison eM d
  let eMT := (Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM
  let eNT := (Algebra.TensorProduct.cancelBaseChange S T K K N).trans eN
  let eCT := (Algebra.TensorProduct.cancelBaseChange S T K K C).trans eC
  let : Module.Free T (T ⊗[S] N) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange S R T T N).toLinearEquiv
  let : Module.Free T (T ⊗[S] C) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange S R T T C).toLinearEquiv
  obtain ⟨qT, hqT⟩ := flatten_retained_map (R := R) (T := T) eN eC qR qK hqR
  let l : M →ₐ[S] C := IsScalarTower.toAlgHom S M C
  let lK : A →ₐ[K] Localization.Away (modelEval eM d) :=
    IsScalarTower.toAlgHom K A (Localization.Away (modelEval eM d))
  have hl := tensor_square_of_points eM eC l lK
    (fun m => tensorAwayComparison_tmul eM d m 1)
  have hfT := rebased_comparison_square (S := S) (R := T) eM eN f fK hf
  have hlT := rebased_comparison_square (S := S) (R := T) eM eC l lK hl
  let fT := Algebra.TensorProduct.lTensor (S := T) T f
  let lT := Algebra.TensorProduct.lTensor (S := T) T l
  obtain ⟨hiq, heq⟩ := map_equations_of_injections
    (modelEval eMT) (modelEval eNT) (modelEval eCT)
    fT.toRingHom lT.toRingHom qT.toRingHom fK.toRingHom lK.toRingHom qK.toRingHom
    (modelEval_injective eNT hi) (modelEval_injective eCT hi) hqK
    (points_of_tensor_square eMT eNT fT fK hfT)
    (points_of_tensor_square eMT eCT lT lK hlT) hqT
    (congrArg AlgHom.toRingHom hqf)
  let dT : T ⊗[S] M := (1 : T) ⊗ₜ[S] d
  let eAway := IsLocalization.Away.tensorProductEquivTMulRight S T d C
  let qAway : T ⊗[S] N →+* Localization.Away dT :=
    eAway.toRingHom.comp qT.toRingHom
  have hqAway : Function.Injective qAway := eAway.injective.comp hiq
  have hsq : qAway.comp fT.toRingHom =
      algebraMap (T ⊗[S] M) (Localization.Away dT) := by
    apply RingHom.ext
    intro x
    exact (congrArg eAway (DFunLike.congr_fun heq x)).trans
      (DFunLike.congr_fun (tensor_away_square (S := S) (T := T) d) x)
  let E := RingEquiv.ofBijective (Localization.awayMap fT.toRingHom dT)
    (away_bijective_of_injection fT.toRingHom dT qAway hqAway hsq)
  refine ⟨E, RingHom.ext fun x => ?_⟩
  exact IsLocalization.map_eq
    (M := Submonoid.powers dT) (T := Submonoid.powers (fT dT))
    (S := Localization.Away dT) (Q := Localization.Away (fT dT)) (g := fT.toRingHom)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, (map_pow fT.toRingHom dT n).symm⟩) x

/-- A principal-localization comparison descends to scalar extensions of the
prescribed algebra models, with its original algebra-map triangle. -/
theorem exists_away_comparison_stage {K M N A B : Type u}
    [Field K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra S N] [Algebra.FinitePresentation S M]
    [Algebra.FinitePresentation S N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (f : M →ₐ[S] N) (fK : A →ₐ[K] B) (d : M)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp eM.toAlgHom)
    (qK : B →ₐ[K] Localization.Away (modelEval eM d))
    (hqK : Function.Injective qK)
    (hqf : qK.comp fK = IsScalarTower.toAlgHom K A (Localization.Away (modelEval eM d))) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      T.FG ∧ awayModelData (Algebra.TensorProduct.lTensor (S := T) T f)
        ((1 : T) ⊗ₜ[S] d) := by
  let C := Localization.Away d
  let eC := tensorAwayComparison eM d
  obtain ⟨R, hSR, hR, qR, hqR⟩ := retain_map S hS eN eC qK
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  obtain ⟨T, hT, hRT, hn, hc⟩ := exists_free_pair_models
    (A := R ⊗[S] N) (B := R ⊗[S] C) R hR
  let hST : S ≤ T := hSR.trans hRT
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  let : Module.Free T (T ⊗[R] (R ⊗[S] N)) := hn
  let : Module.Free T (T ⊗[R] (R ⊗[S] C)) := hc
  have hp := away_packet (S := S) (R := R) (T := T) (K := K) eM eN f fK d hf qK hqK hqf qR hqR
    (Subtype.val_injective : Function.Injective (algebraMap T K))
  exact ⟨T, hST, hT, hp⟩

private theorem away_transport {R M N M' N' : Type u}
    [CommRing R] [CommRing M] [CommRing N] [CommRing M'] [CommRing N']
    [Algebra R M] [Algebra R N] [Algebra R M'] [Algebra R N']
    (cM : M ≃ₐ[R] M') (cN : N ≃ₐ[R] N')
    (f : M →ₐ[R] N) (f' : M' →ₐ[R] N')
    (hf : cN.toAlgHom.comp f = f'.comp cM.toAlgHom) (d : M)
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap M (Localization.Away d)) =
      (algebraMap N (Localization.Away (f d))).comp f.toRingHom) :
    ∃ E' : Localization.Away (cM d) ≃+* Localization.Away (f' (cM d)),
      E'.toRingHom.comp (algebraMap M' (Localization.Away (cM d))) =
        (algebraMap N' (Localization.Away (f' (cM d)))).comp f'.toRingHom := by
  have hd : cN (f d) = f' (cM d) := DFunLike.congr_fun hf d
  let eM := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers d) (T := Submonoid.powers (cM d))
    (Localization.Away d) (Localization.Away (cM d)) cM.toRingEquiv
    (Submonoid.map_powers cM.toRingEquiv d)
  let eN := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (f d)) (T := Submonoid.powers (f' (cM d)))
    (Localization.Away (f d)) (Localization.Away (f' (cM d))) cN.toRingEquiv
    (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hd)
  let E' := eM.symm.trans (E.trans eN)
  refine ⟨E', RingHom.ext fun x => ?_⟩
  have hm : eM.symm (algebraMap M' (Localization.Away (cM d)) x) =
      algebraMap M (Localization.Away d) (cM.symm x) := by
    apply eM.injective
    rw [eM.apply_symm_apply]
    exact (IsLocalization.ringEquivOfRingEquiv_eq _ (cM.symm x)).trans
      (congrArg (algebraMap M' (Localization.Away (cM d))) (cM.apply_symm_apply x)) |>.symm
  change eN (E (eM.symm (algebraMap M' (Localization.Away (cM d)) x))) =
    algebraMap N' (Localization.Away (f' (cM d))) (f' x)
  rw [hm]
  have hx := DFunLike.congr_fun hE (cM.symm x)
  change E (algebraMap M (Localization.Away d) (cM.symm x)) =
    algebraMap N (Localization.Away (f d)) (f (cM.symm x)) at hx
  rw [hx]
  exact (IsLocalization.ringEquivOfRingEquiv_eq _ (f (cM.symm x))).trans
    (congrArg (algebraMap N' (Localization.Away (f' (cM d))))
      ((DFunLike.congr_fun hf (cM.symm x)).trans (congrArg f' (cM.apply_symm_apply x))))

private theorem away_inverse_eq {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (d d' : A) (h : d' = d) (hd : IsRegular (f d))
    (E : Localization.Away d ≃+* Localization.Away (f d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (f d))).comp f.toRingHom) :
    ∃ q : B →ₐ[K] Localization.Away d', Function.Injective q ∧
      q.comp f = IsScalarTower.toAlgHom K A (Localization.Away d') := by
  subst d'
  exact away_inverse f d hd E hE

private theorem modelEval_pure_rebase {S R K M A : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S M] [Algebra K A] (e : K ⊗[S] M ≃ₐ[K] A) (m : M) :
    modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans e)
      ((1 : R) ⊗ₜ[S] m) = modelEval e m := by
  simp [modelEval]

private def retainedAwayData {S T K M N A : Type u}
    [CommRing S] [CommRing T] [CommRing K] [CommRing M] [CommRing N] [CommRing A]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    [Algebra S M] [Algebra S N] [Algebra K A]
    (eM : K ⊗[S] M ≃ₐ[K] A) (f : M →ₐ[S] N) (d : A) : Prop :=
  ∃ dT : T ⊗[S] M,
    modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM) dT = d ∧
      awayModelData (Algebra.TensorProduct.lTensor (S := T) T f) dT

private theorem retained_away_packet {S R T K M N A : Type u}
    [CommRing S] [CommRing R] [CommRing T] [CommRing K]
    [CommRing M] [CommRing N] [CommRing A]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]
    [Algebra S K] [Algebra R K] [Algebra T K]
    [IsScalarTower S R K] [IsScalarTower S T K] [IsScalarTower R T K]
    [Algebra S M] [Algebra S N] [Algebra K A]
    (eM : K ⊗[S] M ≃ₐ[K] A) (f : M →ₐ[S] N)
    (dR : R ⊗[S] M) (d : A)
    (hdR : modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM) dR = d)
    (hAway : awayModelData (Algebra.TensorProduct.lTensor (S := T) T
      (Algebra.TensorProduct.lTensor (S := R) R f)) ((1 : T) ⊗ₜ[R] dR)) :
    retainedAwayData (T := T) eM f d := by
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  let fR := Algebra.TensorProduct.lTensor (S := R) R f
  obtain ⟨E', hE'⟩ := hAway
  let cM := Algebra.TensorProduct.cancelBaseChange S R T T M
  let cN := Algebra.TensorProduct.cancelBaseChange S R T T N
  let fT := Algebra.TensorProduct.lTensor (S := T) T f
  let fOuter := Algebra.TensorProduct.lTensor (S := T) T fR
  have hcancel : cN.toAlgHom.comp fOuter = fT.comp cM.toAlgHom := by
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t y =>
        induction y using TensorProduct.inductionOn with
        | tmul r m => rfl
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨ET, hET⟩ := away_transport cM cN fOuter fT hcancel ((1 : T) ⊗ₜ[R] dR) E' hE'
  have hden : modelEval ((Algebra.TensorProduct.cancelBaseChange S T K K M).trans eM)
      (cM ((1 : T) ⊗ₜ[R] dR)) = d :=
    (modelEval_flatten eM ((1 : T) ⊗ₜ[R] dR)).trans
      ((modelEval_pure_rebase eMR dR).trans hdR)
  exact ⟨cM ((1 : T) ⊗ₜ[R] dR), hden, ET, hET⟩

private theorem exists_after_element {K M N A B : Type u}
    [Field K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    (S R : Subalgebra ℤ K) (hR : R.FG) (hSR : S ≤ R)
    [Algebra S M] [Algebra S N] [Algebra.FinitePresentation S M]
    [Algebra.FinitePresentation S N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (f : M →ₐ[S] N) (fK : A →ₐ[K] B)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp eM.toAlgHom)
    (d : A) :
    let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    ∀ dR : R ⊗[S] M,
      modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM) dR = d →
      (∃ qK : B →ₐ[K] Localization.Away
        (modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM) dR),
        Function.Injective qK ∧ qK.comp fK = IsScalarTower.toAlgHom K A
          (Localization.Away (modelEval ((Algebra.TensorProduct.cancelBaseChange S R K K
            M).trans eM) dR))) →
      ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
        let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
        let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
        T.FG ∧ retainedAwayData (T := T) eM f d := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  intro _ _ dR hdR hq
  obtain ⟨qK, hqK, hqf⟩ := hq
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  let eNR := (Algebra.TensorProduct.cancelBaseChange S R K K N).trans eN
  let fR := Algebra.TensorProduct.lTensor (S := R) R f
  have hfR := rebased_comparison_square (S := S) (R := R) eM eN f fK hf
  obtain ⟨T, hRT, hT, hAway⟩ := exists_away_comparison_stage R hR
    eMR eNR fR fK dR hfR qK hqK hqf
  let hST : S ≤ T := hSR.trans hRT
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  have hp := retained_away_packet (S := S) (R := R) (T := T) eM f dR d hdR hAway
  exact ⟨T, hST, hT, hp⟩

/-- An isomorphism after inverting a field-fibre denominator is retained after
one coefficient extension of the specified algebra models. The lifted
denominator and the original localization-map triangle are retained together. -/
theorem exists_retained_away {K M N A B : Type u}
    [Field K] [CommRing M] [CommRing N] [CommRing A] [CommRing B]
    (S : Subalgebra ℤ K) (hS : S.FG)
    [Algebra S M] [Algebra S N] [Algebra.FinitePresentation S M]
    [Algebra.FinitePresentation S N] [Algebra K A] [Algebra K B]
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (f : M →ₐ[S] N) (fK : A →ₐ[K] B)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f) =
      fK.comp eM.toAlgHom)
    (d : A) (hd : IsRegular (fK d))
    (E : Localization.Away d ≃+* Localization.Away (fK d))
    (hE : E.toRingHom.comp (algebraMap A (Localization.Away d)) =
      (algebraMap B (Localization.Away (fK d))).comp fK.toRingHom) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ retainedAwayData (T := T) eM f d := by
  obtain ⟨R, hSR, hR, dR, hdR⟩ := retain_element S hS eM d
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let eMR := (Algebra.TensorProduct.cancelBaseChange S R K K M).trans eM
  have hdR' : modelEval eMR dR = d := (modelEval_rebase eM dR).trans hdR
  have hq := away_inverse_eq fK d (modelEval eMR dR) hdR' hd E hE
  exact exists_after_element S R hR hSR eM eN f fK hf d dR hdR' hq

end FrobeniusSplitting
