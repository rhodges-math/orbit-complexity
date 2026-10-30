import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSectionMatch
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPullback
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.FramePolynomialModels
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.CoefficientDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Descent of word determinant coefficients

The retained degree-two frame polynomials supply the arithmetic coefficients.
Their exponent-one matching equations follow from the word determinant
section and the injectivity of the coefficient comparison. Thus the retained
section and the word determinant section agree under the scalar matching-line
isomorphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow coefficientSection
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private wordCoefficients_match
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSectionMatch

private theorem scalar_comparison_value {K : Type u} [kField : Field K]
    (S T : Subalgebra ℤ K) (hST : S ≤ T) {I : Type u} [iCat : Category.{u} I]
    (M : I ⥤ CommAlgCat.{u} S) (F : I ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s) :
    letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    ∀ (s : I) (x : T ⊗[S] M.obj s),
      (@scalarDiagramComparison.{u,u,u} K kField S T hST I iCat M F e s)
        ((1 : K) ⊗ₜ[T] x) = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
            (AlgHom.id S (M.obj s)) x) := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  intro s x
  induction x using TensorProduct.inductionOn with
  | tmul t x =>
      rw [@scalarDiagramComparison_tmul.{u,u,u} K kField S T hST I iCat M F e]
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply, mul_one]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
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

private theorem bind_stage {I : Type*} [Preorder I] {i : I}
    {P : ∀ j : I, i ≤ j → Prop}
    {Q : ∀ j : I, i ≤ j → ∀ k : I, j ≤ k → Prop}
    (h : ∃ j : I, ∃ hij : i ≤ j, P j hij)
    (next : ∀ j hij, P j hij → ∃ k : I, ∃ hjk : j ≤ k, Q j hij k hjk) :
    ∃ j : I, ∃ hij : i ≤ j, ∃ k : I, ∃ hjk : j ≤ k, Q j hij k hjk := by
  obtain ⟨j, hij, hj⟩ := h
  obtain ⟨k, hjk, hk⟩ := next j hij hj
  exact ⟨j, hij, k, hjk, hk⟩

private theorem map_stage {I : Type*} [Preorder I] {i : I}
    {P Q : ∀ j : I, i ≤ j → Prop}
    (h : ∃ j : I, ∃ hij : i ≤ j, P j hij)
    (next : ∀ j hij, P j hij → Q j hij) :
    ∃ j : I, ∃ hij : i ≤ j, Q j hij := by
  obtain ⟨j, hij, hj⟩ := h
  exact ⟨j, hij, next j hij hj⟩

private theorem bind_character_data {V D : Sort*} {FG Z : Prop}
    {Eval : V → Prop} {Scalar : V → D → Prop}
    {Cocycle Natural Diagonal Inverse : D → Prop} {Powers : V → D → Prop}
    (h : ∃ v : V, FG ∧ Eval v ∧ ∃ d : D,
      Scalar v d ∧ Cocycle d ∧ Natural d ∧ Diagonal d ∧ Inverse d ∧ Powers v d)
    (next : ∀ v, FG → Eval v → ∀ d,
      Scalar v d → Cocycle d → Natural d → Diagonal d → Inverse d → Powers v d → Z) : Z := by
  obtain ⟨v, hfg, he, d, hs, hc, hn, hd, hi, hp⟩ := h
  exact next v hfg he d hs hc hn hd hi hp

private theorem map_polynomial_data {V D P : Sort*} {H FG : Prop}
    {Eval Injective : V → Prop} {Polynomial : V → P → Prop}
    {Scalar : V → D → Prop} {Cocycle Natural : D → Prop}
    {Singleton : V → P → Prop} {Matching : D → P → Prop}
    (hH : H) (d : D)
    (h : ∃ v : V, FG ∧ Eval v ∧ Injective v ∧ ∃ p : P, Polynomial v p)
    (scalar : ∀ v, Eval v → Scalar v d)
    (cocycle : Cocycle d) (natural : Natural d)
    (singleton : ∀ v p, Polynomial v p → Singleton v p)
    (matching : ∀ v p, Injective v → Scalar v d → Singleton v p → Matching d p) :
    ∃ v : V, H ∧ FG ∧ Injective v ∧ ∃ d' : D,
      Scalar v d' ∧ Cocycle d' ∧ Natural d' ∧ ∃ p : P,
        Polynomial v p ∧ Singleton v p ∧ Matching d' p := by
  obtain ⟨v, hfg, he, hi, p, hp⟩ := h
  have hs := scalar v he
  have ht := singleton v p hp
  exact ⟨v, hH, hfg, hi, d, hs, cocycle, natural, p, hp, ht,
    matching v p hi hs ht⟩

private theorem section_comparison {A : Sort*} {a b c d : A}
    (hab : a = b) (hbc : b = c) (hdc : d = c) : a = d :=
  hab.trans (hbc.trans hdc.symm)

private def selectedIndex (s : {s : Finset J // s.Nonempty}) : J :=
  Classical.choose s.property

private theorem selectedIndex_mem (s : {s : Finset J // s.Nonempty}) :
    selectedIndex s ∈ s.val := Classical.choose_spec s.property

private theorem selectedIndex_singleton (j : J) :
    selectedIndex (singletonIndex j) = j :=
  Finset.mem_singleton.mp (selectedIndex_mem (singletonIndex j))

private def selectedFrame (s : {s : Finset J // s.Nonempty}) :
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ (oppositeUnipotentVariety G).toOver :=
  (algSpec (.of K)).map (F.map (singletonArrow s (selectedIndex s)
    (selectedIndex_mem s))).op ≫ a (selectedIndex s)

private theorem singleton_map_comp {C D A : Type*} [Category C] [Category D]
    (thin : ∀ X Y : C, Subsingleton (X ⟶ Y)) (F : Cᵒᵖ ⥤ D)
    (single : A → C) {Q : D} (a : ∀ j : A, F.obj (op (single j)) ⟶ Q)
    (j k : A) (hk : k = j) (f : single k ⟶ single j) :
    F.map f.op ≫ a k = a j := by
  subst k
  have hf : f = 𝟙 (single j) := (thin _ _).elim _ _
  rw [hf, op_id, CategoryTheory.Functor.map_id, Category.id_comp]

omit hopen hdir in
private theorem selectedChart_singleton (j : J) :
    selectedFrame G F a (singletonIndex j) ≫
        flagChartMap G (point (selectedIndex (singletonIndex j))) =
      a j ≫ flagChartMap G (point j) := by
  have hframe : selectedFrame G F a (singletonIndex j) = a j :=
    singleton_map_comp (fun _ _ => inferInstance) (F.op ⋙ algSpec (.of K))
      singletonIndex a j (selectedIndex (singletonIndex j)) (selectedIndex_singleton j)
      (singletonArrow (singletonIndex j) (selectedIndex (singletonIndex j))
        (selectedIndex_mem (singletonIndex j)))
  exact (congrArg
    (fun f => f ≫ flagChartMap G (point (selectedIndex (singletonIndex j)))) hframe).trans
      (congrArg (fun k => a j ≫ flagChartMap G (point k)) (selectedIndex_singleton j))

/-- The word determinant coefficient in the affine coordinate ring of one chart. -/
def wordRingCoefficient (j : J) : F.obj (singletonIndex j) :=
  (Spec.preimage (a j ≫ flagChartMap G (point j)).left).hom
    (DeterminantSection.positiveDetCoefficient G)

omit hopen hdir in
private theorem wordCoefficient_function (n : ℕ) (j : J) :
    (a j ≫ flagChartMap G (point j)).left.appTop
        (DeterminantSection.positiveDetPowerFunction G n) =
      (Scheme.ΓSpecIso (.of (F.obj (singletonIndex j)))).inv
        ((wordRingCoefficient G F point a j) ^ n) := by
  change (a j ≫ flagChartMap G (point j)).left.appTop
      ((Scheme.ΓSpecIso (.of G.coordinateAlgebra)).inv
        ((DeterminantSection.positiveDetCoefficient G) ^ n)) = _
  exact affine_preimage_coefficient (a j ≫ flagChartMap G (point j)).left
    (DeterminantSection.positiveDetCoefficient G) n

omit hopen hdir in
/-- The affine coefficient section is the original selected word coefficient. -/
theorem wordRingCoefficient_section (n : ℕ) (j : J) :
    ringCoefficientSection F cF j ((wordRingCoefficient G F point a j) ^ n) =
      wordMatchingCoefficient G F cF n point a j :=
  congrArg (relativeCoefficient cF.pt.left (node F cF (singletonIndex j)))
    (wordCoefficient_function G F point a n j).symm

include hopen hdir hcF word q ha hgroup hco hn in
/-- The exponent-one word coefficients satisfy the retained character's
ring matching equations. -/
theorem wordRingCoefficient_matching
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) :
    (F.map (singletonArrow s j hj)).hom (wordRingCoefficient G F point a j) =
      (F.map (singletonArrow s k hk)).hom (wordRingCoefficient G F point a k) *
        (wordTransitionUnit G F beta s j hj k hk : F.obj s) := by
  have he := coefficient_matching_reflects
    (nodeMap F cF (singletonArrow s j hj)) (nodeMap F cF (singletonArrow s k hk))
    ((a j ≫ flagChartMap G (point j)).left.appTop
      (DeterminantSection.positiveDetPowerFunction G 1))
    ((a k ≫ flagChartMap G (point k)).left.appTop
      (DeterminantSection.positiveDetPowerFunction G 1))
    (coefficientSection F cF s ((wordTransitionUnit G F beta s j hj k hk : F.obj s) ^ 1))
    (wordCoefficients_match G F cF hcF word q 1 point a ha beta hgroup hco hn s j hj k hk)
  have hj' := wordCoefficient_function G F point a 1 j
  have hk' := wordCoefficient_function G F point a 1 k
  simp only [pow_one] at hj' hk' he
  rw [hj', hk'] at he
  exact affine_coefficient_reflects
    (CommRingCat.ofHom (F.map (singletonArrow s j hj)).hom.toRingHom)
    (CommRingCat.ofHom (F.map (singletonArrow s k hk)).hom.toRingHom)
    (wordRingCoefficient G F point a j) (wordRingCoefficient G F point a k)
    (wordTransitionUnit G F beta s j hj k hk : F.obj s) he

private theorem wordMatchingSection_from_coefficients (n : ℕ) :
    coefficientMatchingSection F cF (wordTransitionUnit G F beta)
        (wordRingCoefficient G F point a)
        (wordRingCoefficient_matching G F cF hcF word q point a ha beta hgroup hco hn) n =
      wordMatchingSection G F cF hcF word q n point a ha beta hgroup hco hn := by
  apply coordinate_hom_ext F cF (wordTransitionUnit G F beta) n
  intro j
  exact (coefficientMatchingSection_coordinate F cF (wordTransitionUnit G F beta)
    (wordRingCoefficient G F point a)
    (wordRingCoefficient_matching G F cF hcF word q point a ha beta hgroup hco hn) n j).trans
      ((wordRingCoefficient_section G F cF point a n j).trans
        (wordMatchingSection_coordinate G F cF hcF word q n point a ha beta hgroup hco hn j).symm)

variable {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)

/-- The retained arithmetic word coefficient is the top coefficient of its
retained unpowered degree-two frame polynomial. -/
def retainedWordCoefficient (j : J) : N.obj (singletonIndex j) :=
  (P (singletonIndex j)).coeff 2

include hopen hdir hcF word q ha hgroup hco hn hv hd hP in
/-- Injectivity of the prescribed comparison descends matching for the retained
polynomial coefficients; no arithmetic matching equation is assumed. -/
theorem retainedWordCoefficient_match
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) :
    (N.map (singletonArrow s j hj)).hom (retainedWordCoefficient N P j) =
      (N.map (singletonArrow s k hk)).hom (retainedWordCoefficient N P k) *
        (deltaN s j hj k hk : N.obj s) := by
  apply coefficient_cochain_descends
    (N ⋙ forget₂ (CommAlgCat R) CommRingCat)
    (F ⋙ forget₂ (CommAlgCat K) CommRingCat) v hv deltaN
    (retainedWordCoefficient N P)
  · intro t l hl m hm
    dsimp only [retainedWordCoefficient]
    rw [hP l, hP m, hd t l hl m hm]
    exact wordRingCoefficient_matching G F cF hcF word q point a ha beta hgroup hco hn
      t l hl m hm

/-- The retained polynomial coefficients define the arithmetic word section
using their proved matching identities. -/
def retainedWordSection (cN : Cocone (N.op ⋙ algSpec (.of R))) (n : ℕ) :
    SheafOfModules.unit cN.pt.left.ringCatSheaf ⟶ matchingModule N cN deltaN n :=
  coefficientMatchingSection N cN deltaN (retainedWordCoefficient N P)
    (retainedWordCoefficient_match G F cF hcF word q point a ha beta hgroup hco hn
      N v hv deltaN hd P hP) n

variable
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- The section constructed from the retained frame polynomials agrees with
the word determinant section under the two specified matching-line isomorphisms. -/
theorem retainedWord_section_match (n : ℕ) :
    (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
        (Scheme.Modules.pullback qN).map
          (retainedWordSection G F cF hcF word q point a ha beta hgroup hco hn
            N v hv deltaN hd P hP cN n) ≫
        (matchingPullbackIso N F cN hcN cF hcF v qN hqN deltaN
          (wordTransitionUnit G F beta) hd n hcoN hnN hco hn).hom =
      (Scheme.Modules.pullbackObjUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word) ≫
        (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom := by
  exact section_comparison
    (matchingPullbackIso_section N F cN hcN cF hcF v qN hqN deltaN
      (wordTransitionUnit G F beta) hd n hcoN hnN hco hn
      (retainedWordCoefficient N P) (wordRingCoefficient G F point a)
      (retainedWordCoefficient_match G F cF hcF word q point a ha beta hgroup hco hn
        N v hv deltaN hd P hP)
      (wordRingCoefficient_matching G F cF hcF word q point a ha beta hgroup hco hn) hP)
    (wordMatchingSection_from_coefficients G F cF hcF word q point a ha beta hgroup hco hn n)
    (wordDeterminant_section_match G F cF hcF word q n point a ha beta hgroup hco hn)

end SchubertGeometry.RetainedCharacter
