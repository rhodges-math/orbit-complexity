import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarData
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Original coefficients through the word-induction extension

One coefficient extension contains the next simple-root polynomial on the
scalar extension of the given diagram. Its injective comparison identifies the
transition cochain and singleton highest coefficients with the scalar images
of the prior-word data.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private selectedIndex selectedFrame selectedChart_singleton from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent

namespace SchubertGeometry.RetainedCharacter

private theorem coefficient_image_eq {A B C : Type u}
    (f : A → B) (g : B → C) (h : A → C)
    (hg : Function.Injective g) (hcomp : ∀ x, g (f x) = h x)
    (x : A) (y : B) (hy : g y = h x) : y = f x :=
  hg (hy.trans (hcomp x).symm)

private theorem scalar_evaluation {S R K A B : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S A] [Algebra K B]
    (e : K ⊗[S] A ≃ₐ[K] B) (v : R ⊗[S] A →+* B)
    (hv : ∀ x, v x = e (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom S R K) (AlgHom.id S A) x)) (x : A) :
    v ((1 : R) ⊗ₜ[S] x) = e ((1 : K) ⊗ₜ[S] x) := by
  rw [hv, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/-- The next root polynomial lies on one coefficient extension of the given
word diagram, with transition units and highest coefficients equal to the
scalar images of the prior-word data. -/
theorem exists_word_induction_coefficients {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (.op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    [jFinite : Finite J]
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [mFP : ∀ s, Algebra.FinitePresentation S (M.obj s)]
    [mSmooth : ∀ s, Algebra.Smooth S (M.obj s)]
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (M.obj s)ˣ)
    (hdelta : ∀ s j hj k hk, e s ((1 : K) ⊗ₜ[S] (delta s j hj k hk : M.obj s)) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (r : ∀ j : J, M.obj (singletonIndex j))
    (hr : ∀ j, e (singletonIndex j) ((1 : K) ⊗ₜ[S] r j) =
      wordRingCoefficient G F point a j) :
  ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    let N := fixedFibreDiagram (R := R) (M := R) M
    let mu := fixedScalarMap S R M
    let d := matchingScalarUnits M N mu delta
      ∃ v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
          F ⋙ forget₂ (CommAlgCat K) CommRingCat,
        R.FG ∧
        (∀ s x, (v.app s).hom x = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M.obj s)) x)) ∧
        (∀ s x, (v.app s).hom ((mu.app s).hom x) = e s ((1 : K) ⊗ₜ[S] x)) ∧
        (∀ s, Function.Injective (v.app s).hom) ∧
        (∀ s j hj k hk, (v.app s).hom (d s j hj k hk : N.obj s) =
          (wordTransitionUnit G F beta s j hj k hk : F.obj s)) ∧
        (∀ s j hj k hk l hl, d s j hj l hl = d s k hk l hl * d s j hj k hk) ∧
        (∀ s t (f : s ⟶ t) j hj k hk,
          Units.map (N.map f).hom.toMonoidHom (d s j hj k hk) =
            d t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
        ∃ P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s),
          (∀ s, (P s).natDegree ≤ 2 ∧
            Polynomial.map (v.app s).hom (P s) =
              Polynomial.map (Spec.preimage (selectedFrame G F a s ≫
                flagChartMap G (point (selectedIndex s))).left).hom
                  (DeterminantSection.simpleFramePolynomial G i
                    (DeterminantSection.positiveDetCoefficient G)) ∧
            (v.app s).hom ((P s).coeff 2) =
              (Spec.preimage (selectedFrame G F a s ≫
                flagChartMap G (point (selectedIndex s))).left).hom
                  (DeterminantSection.positiveDetCoefficient G) ∧
            ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n) ∧
          (∀ j, (P (singletonIndex j)).coeff 2 =
            (mu.app (singletonIndex j)).hom (r j)) ∧
          (∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
            wordRingCoefficient G F point a j) ∧
          ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
            (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
              (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
                (d s j hj k hk : N.obj s) := by
  have coefficients :=
    @DeterminantSection.exists_retained_frame_polynomials.{u,u}
      K kField kClosed kZero G J jFinite i S hS M mFP mSmooth F e he
      (fun s => point (selectedIndex s)) (fun s => selectedFrame G F a s)
  obtain ⟨R, hSR, hData⟩ := coefficients
  refine ⟨R, hSR, ?_⟩
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N := fixedFibreDiagram (R := R) (M := R) M
  let mu := fixedScalarMap S R M
  let d := matchingScalarUnits M N mu delta
  obtain ⟨v, hR, hv, hi, P, hP⟩ := hData
  have hvalue : ∀ s x, (v.app s).hom ((mu.app s).hom x) =
      e s ((1 : K) ⊗ₜ[S] x) := by
    intro s x
    exact scalar_evaluation (e s) (v.app s).hom (hv s) x
  have hd : ∀ s j hj k hk, (v.app s).hom (d s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s) := by
    intro s j hj k hk
    exact (hvalue s (delta s j hj k hk : M.obj s)).trans (hdelta s j hj k hk)
  have hcoD : ∀ s j hj k hk l hl,
      d s j hj l hl = d s k hk l hl * d s j hj k hk := by
    intro s j hj k hk l hl
    apply Units.ext
    apply hi s
    change (v.app s).hom (d s j hj l hl : N.obj s) =
      (v.app s).hom ((d s k hk l hl : N.obj s) * (d s j hj k hk : N.obj s))
    rw [map_mul, hd, hd, hd]
    exact congrArg (fun z : (F.obj s)ˣ => (z : F.obj s)) (hco s j hj k hk l hl)
  have hnD : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (d s j hj k hk) =
        d t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
    intro s t f j hj k hk
    apply Units.ext
    apply hi t
    have hvf := congrArg (fun z :
        (N ⋙ forget₂ (CommAlgCat R) CommRingCat).obj s ⟶
          (F ⋙ forget₂ (CommAlgCat K) CommRingCat).obj t =>
        z.hom (d s j hj k hk : N.obj s)) (v.naturality f)
    change (v.app t).hom ((N.map f).hom (d s j hj k hk : N.obj s)) =
      (F.map f).hom ((v.app s).hom (d s j hj k hk : N.obj s)) at hvf
    change (v.app t).hom ((N.map f).hom (d s j hj k hk : N.obj s)) =
      (v.app t).hom (d t j ((leOfHom f) hj) k ((leOfHom f) hk) : N.obj t)
    rw [hvf, hd, hd]
    exact congrArg (fun z : (F.obj t)ˣ => (z : F.obj t)) (hn s t f j hj k hk)
  have hsingle : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j := by
    intro j
    have hs := selectedChart_singleton G F point a j
    simpa only [hs, wordRingCoefficient] using (hP (singletonIndex j)).2.2.1
  have htop : ∀ j, (P (singletonIndex j)).coeff 2 =
      (mu.app (singletonIndex j)).hom (r j) := by
    intro j
    exact coefficient_image_eq (mu.app (singletonIndex j)).hom
      (v.app (singletonIndex j)).hom
      (fun x => e (singletonIndex j) ((1 : K) ⊗ₜ[S] x))
      (hi (singletonIndex j)) (hvalue (singletonIndex j))
      (r j) ((P (singletonIndex j)).coeff 2) ((hsingle j).trans (hr j).symm)
  have hmatch : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
          (d s j hj k hk : N.obj s) := by
    intro s j hj k hk
    simpa only [retainedWordCoefficient] using
      (@retainedWordCoefficient_match.{u} K kField kClosed kZero G J F
        hopen hdir cF hcF word q point a ha beta hgroup hco hn
        R (inferInstance : CommRing R) N v hi d hd P hsingle s j hj k hk)
  exact ⟨v, hR, hv, hvalue, hi, hd, hcoD, hnD, P, hP, htop, hsingle, hmatch⟩

end SchubertGeometry.RetainedCharacter
