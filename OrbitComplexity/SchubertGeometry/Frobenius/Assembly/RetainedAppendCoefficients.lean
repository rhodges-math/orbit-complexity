import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarData
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retaining the matching coefficients on the append atlas

The append atlas and the preceding matching units and quadratic coefficients
use the same coefficient extension. The tensor comparisons preserve every
polynomial power and every coefficient power.
-/

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private tensor_coordinate_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas

section Coefficients
variable {S R K J : Type u}
  [CommRing S] [CommRing R] [CommRing K]
  [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
  (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
  (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
  (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
  (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
    (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
  (P : ∀ j, Polynomial (N.obj (singletonIndex j)))

/-- The matching equations and all powers on the canonical tensor diagram. -/
def appendCoefficientSpec : Prop :=
  let M := fixedFibreDiagram (R := R) (M := R) N
  let v := fixedScalarMap S R N
  let eR := fun s ↦ (Algebra.TensorProduct.cancelBaseChange S R K K (N.obj s)).trans (e s)
  let deltaR := matchingScalarUnits N M v delta
  let PR := matchingScalarPolynomial N M v P
  (∀ s j hj k hk l hl,
    deltaR s j hj l hl = deltaR s k hk l hl * deltaR s j hj k hk) ∧
  (∀ s t (f : s ⟶ t) j hj k hk,
    Units.map (M.map f).hom.toMonoidHom (deltaR s j hj k hk) =
      deltaR t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
  (∀ j, (PR j).natDegree ≤ 2) ∧
  (∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
    (M.map (singletonArrow s j hj)).hom ((PR j).coeff 2) =
      (M.map (singletonArrow s k hk)).hom ((PR k).coeff 2) *
        (deltaR s j hj k hk : M.obj s)) ∧
  (∀ j n, PR j ^ n = Polynomial.map (v.app (singletonIndex j)).hom (P j ^ n)) ∧
  (∀ j k n, (PR j).coeff k ^ n = (v.app (singletonIndex j)).hom ((P j).coeff k ^ n)) ∧
  (∀ j n k, (PR j ^ n).coeff k = (v.app (singletonIndex j)).hom ((P j ^ n).coeff k)) ∧
  (∀ s (x : N.obj s) n, eR s ((1 : K) ⊗ₜ[R]
      (((Algebra.TensorProduct.includeRight : N.obj s →ₐ[S] R ⊗[S] N.obj s) x) ^ n)) =
    e s ((1 : K) ⊗ₜ[S] (x ^ n))) ∧
  ∀ j n, Polynomial.map
      ((eR (singletonIndex j)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        (PR j ^ n) =
    Polynomial.map
      ((e (singletonIndex j)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        (P j ^ n)

private theorem append_coefficient_packet
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hP : ∀ j, (P j).natDegree ≤ 2)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) *
          (delta s j hj k hk : N.obj s)) : appendCoefficientSpec (R := R) N F e delta P := by
  let M := fixedFibreDiagram (R := R) (M := R) N
  let v := fixedScalarMap S R N
  let eR := fun s ↦ (Algebra.TensorProduct.cancelBaseChange S R K K (N.obj s)).trans (e s)
  refine ⟨matchingScalarUnits_cocycle N M v delta hco,
    matchingScalarUnits_natural N M v delta hn,
    (fun j ↦ matchingScalarPolynomial_degree N M v P hP j),
    matchingScalarPolynomial_leading N M v delta P hr,
    matchingScalarPolynomial_pow N M v P,
    matchingScalarPolynomial_coeff_pow N M v P,
    matchingScalarPolynomial_pow_coeff N M v P, ?_, ?_⟩
  · intro s x n
    rw [← map_pow
      (Algebra.TensorProduct.includeRight : N.obj s →ₐ[S] R ⊗[S] N.obj s) x n]
    change (e s) (Algebra.TensorProduct.cancelBaseChange S R K K (N.obj s)
        ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] (x ^ n)))) =
      e s ((1 : K) ⊗ₜ[S] (x ^ n))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  · intro j n
    rw [matchingScalarPolynomial_pow, Polynomial.map_map]
    exact congrArg (fun f : N.obj (singletonIndex j) →+* F.obj (singletonIndex j) ↦
      Polynomial.map f (P j ^ n)) (tensor_coordinate_factor (R := R) (e (singletonIndex j)))

end Coefficients

/-- The constructed append atlas retains the given matching units and
quadratic section coefficients, including their values in every power. -/
theorem exists_retained_append_coefficients {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    [nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [nDir : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hchart : ∀ s j hj k hk,
      (p s j hj ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c j =
      (overlapTwist (Y := (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) (beta s j hj k hk)).hom ≫
        (p s k hk ⊗ₘ 𝟙 _) ≫ c k)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (hb : IsColimit (Cocone.mk (bsdhScheme G word) b))
    (hbbase : ∀ s, b.app (.op s) ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hcart : ∀ s, IsPullback
      (fst ((algSpec (.of K)).obj (.op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (.op s)) (bsdhAppendFst G word i))
    (cG : Cocone (N.op ⋙ algSpec (.of S)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hbmodel : ∀ s, b.app (.op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left)

    [finiteJ : Finite J]
    [nodeFP : ∀ s, Algebra.FinitePresentation S (N.obj s)]
    [nodeSmooth : ∀ s, Algebra.Smooth S (N.obj s)]
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hP : ∀ j, (P j).natDegree ≤ 2)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) *
          (delta s j hj k hk : N.obj s))
    (hcG : IsColimit cG) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ extendedAppendAtlasSpec (T := T) G word i V₀ F N e p c beta sel b cG m₀ hST ∧
        appendCoefficientSpec (R := T) N F e delta P := by
  obtain ⟨T, hST, H⟩ := @exists_retained_append_atlas.{u} K kField kClosed kZero S hS
    G word i J V₀ F N e he fOpen fDir nOpen nDir p c hpn beta
    hchart hnatural hbeta sel b hb hbbase hcart cG m₀ hm₀ hbmodel
    finiteJ nodeFP nodeSmooth hcG
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  obtain ⟨hT, hAtlas⟩ := H
  exact ⟨T, hST, hT, hAtlas, append_coefficient_packet N F e delta P hco hn hP hr⟩

end SchubertGeometry
