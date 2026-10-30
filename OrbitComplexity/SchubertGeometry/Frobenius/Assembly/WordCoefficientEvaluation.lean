import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Evaluation of retained word coefficients

The two finite coefficient extensions retain the canonical tensor-evaluation
formula together with their full character units and determinant polynomials.
The comparison therefore remains tied to the original coordinate diagram.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private bind_stage map_stage bind_character_data selectedIndex selectedFrame
  selectedChart_singleton scalar_comparison_value
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent

private theorem retain_raw_data {V D P : Sort*} {H FG : Prop}
    {Eval Injective : V → Prop} {Polynomial : V → P → Prop}
    {Scalar : V → D → Prop} {Cocycle Natural : D → Prop}
    {Singleton : V → P → Prop} {Matching : D → P → Prop}
    (hH : H) (d : D)
    (h : ∃ v : V, FG ∧ Eval v ∧ Injective v ∧ ∃ p : P, Polynomial v p)
    (scalar : ∀ v, Eval v → Scalar v d)
    (cocycle : Cocycle d) (natural : Natural d)
    (singleton : ∀ v p, Polynomial v p → Singleton v p)
    (matching : ∀ v p, Injective v → Scalar v d → Singleton v p → Matching d p) :
    ∃ v : V, H ∧ FG ∧ Eval v ∧ Injective v ∧ ∃ d' : D,
      Scalar v d' ∧ Cocycle d' ∧ Natural d' ∧ ∃ p : P,
        Polynomial v p ∧ Singleton v p ∧ Matching d' p := by
  obtain ⟨v, hfg, he, hi, p, hp⟩ := h
  have hs := scalar v he
  have ht := singleton v p hp
  exact ⟨v, hH, hfg, he, hi, d, hs, cocycle, natural, p, hp, ht,
    matching v p hi hs ht⟩

section

variable {T R K J : Type u} [CommRing T] [CommRing R] [CommRing K]
    [Algebra T R] [Algebra R K] [Algebra T K] [IsScalarTower T R K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} T)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[T] N.obj s ≃ₐ[K] F.obj s)

private def rawData (FG : Prop)
    (Poly :
      (fixedFibreDiagram (R := R) (M := R) N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat) →
      (∀ s : {s : Finset J // s.Nonempty},
        Polynomial ((fixedFibreDiagram (R := R) (M := R) N).obj s)) → Prop) : Prop :=
  let NR := fixedFibreDiagram (R := R) (M := R) N
  ∃ v : NR ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat,
    FG ∧
    (∀ s x, (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
        (AlgHom.id T (N.obj s)) x)) ∧
    (∀ s, Function.Injective (v.app s).hom) ∧
    ∃ P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (NR.obj s), Poly v P

private def wordCoefficientData (H FG : Prop)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (rF : ∀ j : J, F.obj (singletonIndex j))
    (Poly :
      (fixedFibreDiagram (R := R) (M := R) N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat) →
      (∀ s : {s : Finset J // s.Nonempty},
        Polynomial ((fixedFibreDiagram (R := R) (M := R) N).obj s)) → Prop) : Prop :=
  let NR := fixedFibreDiagram (R := R) (M := R) N
  ∃ v : NR ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat,
    H ∧ FG ∧
    (∀ s x, (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
        (AlgHom.id T (N.obj s)) x)) ∧
    (∀ s, Function.Injective (v.app s).hom) ∧
    ∃ delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), (NR.obj s)ˣ,
      (∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : NR.obj s) =
        (deltaF s j hj k hk : F.obj s)) ∧
      (∀ s j hj k hk l hl,
        delta s j hj l hl = delta s k hk l hl * delta s j hj k hk) ∧
      (∀ s t (f : s ⟶ t) j hj k hk,
        Units.map (NR.map f).hom.toMonoidHom (delta s j hj k hk) =
          delta t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
      ∃ P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (NR.obj s),
        Poly v P ∧
        (∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) = rF j) ∧
        ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
          (NR.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
            (NR.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
              (delta s j hj k hk : NR.obj s)

/-- The complete inner coefficient construction is over arbitrary coefficient rings. -/
private theorem generic_inner_pack
    (vT : N ⋙ forget₂ (CommAlgCat T) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hvT : ∀ s x, e s ((1 : K) ⊗ₜ[T] x) = (vT.app s).hom x)
    (deltaT : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hdT : ∀ s j hj k hk, (vT.app s).hom (deltaT s j hj k hk : N.obj s) =
      (deltaF s j hj k hk : F.obj s))
    (hcoT : ∀ s j hj k hk l hl,
      deltaT s j hj l hl = deltaT s k hk l hl * deltaT s j hj k hk)
    (hnT : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaT s j hj k hk) =
        deltaT t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (rF : ∀ j : J, F.obj (singletonIndex j))
    (hrF : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (F.map (singletonArrow s j hj)).hom (rF j) =
        (F.map (singletonArrow s k hk)).hom (rF k) * (deltaF s j hj k hk : F.obj s))
    {H FG : Prop} (hH : H)
    (Poly :
      (fixedFibreDiagram (R := R) (M := R) N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat) →
      (∀ s : {s : Finset J // s.Nonempty},
        Polynomial ((fixedFibreDiagram (R := R) (M := R) N).obj s)) → Prop)
    (hraw : rawData (R := R) N F e FG Poly)
    (hsingle : ∀ v P, Poly v P →
      ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) = rF j) :
    wordCoefficientData (R := R) N F e H FG deltaF rF Poly := by
  let NR := fixedFibreDiagram (R := R) (M := R) N
  let w := scalarCoefficientMap (T := R) N
  let delta := unitCoefficientImage
    (N ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (NR ⋙ forget₂ (CommAlgCat R) CommRingCat) w deltaT
  have hco := unitCoefficientImage_cocycle
    (N ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (NR ⋙ forget₂ (CommAlgCat R) CommRingCat) w deltaT hcoT
  have hn := unitCoefficientImage_natural
    (N ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (NR ⋙ forget₂ (CommAlgCat R) CommRingCat) w deltaT hnT
  exact retain_raw_data hH delta hraw
    (fun v hv => by
      intro s j hj k hk
      change (v.app s).hom ((1 : R) ⊗ₜ[T] (deltaT s j hj k hk : N.obj s)) = _
      exact (scalarEvaluation_compatible (e s) (vT.app s).hom (v.app s).hom
        (hvT s) (hv s) (deltaT s j hj k hk : N.obj s)).trans (hdT s j hj k hk))
    hco hn hsingle
    (fun v P hinj hd hs => by
      apply coefficient_cochain_descends
        (NR ⋙ forget₂ (CommAlgCat R) CommRingCat)
        (F ⋙ forget₂ (CommAlgCat K) CommRingCat) v hinj delta
        (fun j => (P (singletonIndex j)).coeff 2)
      intro s j hj k hk
      rw [hs j, hs k, hd s j hj k hk]
      exact hrF s j hj k hk)

end

private def characterData {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (S : Subalgebra ℤ K)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let MT := fixedFibreDiagram (R := T) (M := T) M
  let delta := fun s j hj k hk =>
    ProjectiveLine.positiveBorelSection G (F.obj s) (beta s j hj k hk)
  ∃ v : MT ⋙ forget₂ (CommAlgCat T) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat,
    T.FG ∧
    (∀ s x, (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S T K)
        (AlgHom.id S (M.obj s)) x)) ∧
    ∃ d : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), (MT.obj s)ˣ,
      (∀ s j hj k hk, (v.app s).hom (d s j hj k hk : MT.obj s) =
        (delta s j hj k hk : F.obj s)) ∧
      (∀ s j hj k hk l hl,
        d s j hj l hl = d s k hk l hl * d s j hj k hk) ∧
      (∀ s t (f : s ⟶ t) j hj k hk,
        Units.map (MT.map f).hom.toMonoidHom (d s j hj k hk) =
          d t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
      (∀ s j hj, d s j hj j hj = 1) ∧
      (∀ s j hj k hk, d s k hk j hj = (d s j hj k hk)⁻¹) ∧
      ∀ n : ℕ,
        (∀ s j hj k hk, (v.app s).hom ((d s j hj k hk : MT.obj s) ^ n) =
          (delta s j hj k hk : F.obj s) ^ n) ∧
        (∀ s j hj k hk l hl,
          (d s j hj l hl) ^ n = (d s k hk l hl) ^ n * (d s j hj k hk) ^ n) ∧
        ∀ s t (f : s ⟶ t) j hj k hk,
          Units.map (MT.map f).hom.toMonoidHom ((d s j hj k hk) ^ n) =
            (d t j ((leOfHom f) hj) k ((leOfHom f) hk)) ^ n

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

private def wordPolynomialData (i : G.rootBase.support)
    {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s)) : Prop :=
  ∀ s, (P s).natDegree ≤ 2 ∧
    Polynomial.map (v.app s).hom (P s) =
      Polynomial.map (Spec.preimage (selectedFrame G F a s ≫
        flagChartMap G (point (selectedIndex s))).left).hom
          (DeterminantSection.simpleFramePolynomial G i
            (DeterminantSection.positiveDetCoefficient G)) ∧
    (v.app s).hom ((P s).coeff 2) =
      (Spec.preimage (selectedFrame G F a s ≫
        flagChartMap G (point (selectedIndex s))).left).hom
          (DeterminantSection.positiveDetCoefficient G) ∧
    ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n

private def polynomialStageData (i : G.rootBase.support)
    (S : Subalgebra ℤ K)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (R' : Subalgebra ℤ K) (hTR : T ≤ R') : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let MT := fixedFibreDiagram (R := T) (M := T) M
  letI : Algebra T R' := (Subalgebra.inclusion hTR).toAlgebra
  letI : IsScalarTower T R' K := Subalgebra.inclusion.isScalarTower_right hTR K
  let N' := fixedFibreDiagram (R := R') (M := R') MT
  rawData (R := R') MT F (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e) R'.FG (wordPolynomialData G F point a i N')

private def coefficientStageResult (i : G.rootBase.support)
    (S : Subalgebra ℤ K)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (R' : Subalgebra ℤ K) (hTR : T ≤ R') : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let MT := fixedFibreDiagram (R := T) (M := T) M
  letI : Algebra T R' := (Subalgebra.inclusion hTR).toAlgebra
  letI : IsScalarTower T R' K := Subalgebra.inclusion.isScalarTower_right hTR K
  let N' := fixedFibreDiagram (R := R') (M := R') MT
  wordCoefficientData (R := R') MT F (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e) T.FG R'.FG (wordTransitionUnit G F beta)
    (wordRingCoefficient G F point a) (wordPolynomialData G F point a i N')

private def indexedStageResult (i : G.rootBase.support)
    (S : Subalgebra ℤ K)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  ∃ (R' : Subalgebra ℤ K) (hTR : T ≤ R'),
    coefficientStageResult G F point a beta i S M e T hST R' hTR

include hopen hdir hcF word q ha hgroup hco hn in
/-- The chosen two-stage coefficient extension retains its canonical evaluation
formula, full character cocycle, and degree-two determinant equations. -/
private theorem exists_indexed_stage [Finite J]
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (M.obj s)] [∀ s, Algebra.Smooth S (M.obj s)]
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      indexedStageResult G F point a beta i S M e T hST := by
  exact map_stage
    (P := characterData G S M F e beta)
    (Q := indexedStageResult G F point a beta i S M e)
    (exists_chosen_borel_character G S hS M F e he beta hnatural hbeta)
    (fun T hST hTdata => by
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      let MT := fixedFibreDiagram (R := T) (M := T) M
      let : ∀ s, Algebra.FinitePresentation T (MT.obj s) := fun s => by
        change Algebra.FinitePresentation T (T ⊗[S] M.obj s)
        infer_instance
      let : ∀ s, Algebra.Smooth T (MT.obj s) := fun s => by
        change Algebra.Smooth T (T ⊗[S] M.obj s)
        infer_instance
      exact bind_character_data
        (Z := indexedStageResult G F point a beta i S M e T hST) hTdata
        (fun vT hT hvT deltaT hdT hcoT hnT _hdiagT _hinvT _hpowersT => by
          have heT := @scalarDiagramComparison_natural.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e he
          have hvalT (s : {s : Finset J // s.Nonempty}) (x : MT.obj s) :
              (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e) s ((1 : K) ⊗ₜ[T] x) = (vT.app s).hom x :=
            (@scalar_comparison_value.{u} K kField S T hST
              {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e s x).trans (hvT s x).symm
          exact map_stage
            (P := polynomialStageData G F point a i S M e T hST)
            (Q := coefficientStageResult G F point a beta i S M e T hST)
            (DeterminantSection.exists_retained_frame_polynomials G i T hT MT F
                (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e) heT
              (fun s => point (selectedIndex s)) (selectedFrame G F a))
            (fun R' hTR hRdata => by
              let : Algebra T R' := (Subalgebra.inclusion hTR).toAlgebra
              let : IsScalarTower T R' K := Subalgebra.inclusion.isScalarTower_right hTR K
              let N' := fixedFibreDiagram (R := R') (M := R') MT
              exact generic_inner_pack (T := T) (R := R') (K := K) MT F
                  (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e)
                vT hvalT deltaT (wordTransitionUnit G F beta) hdT hcoT hnT
                (wordRingCoefficient G F point a)
                (wordRingCoefficient_matching G F cF hcF word q point a ha beta hgroup hco hn)
                (H := T.FG) (FG := R'.FG) hT
                (wordPolynomialData G F point a i N') hRdata
                (fun v' P' hP' => by
                  intro j
                  exact ((hP' (singletonIndex j)).2.2.1).trans
                    (congrArg
                      (fun f : Spec (.of (F.obj (singletonIndex j))) ⟶ Spec (.of
                          G.coordinateAlgebra) =>
                        (Spec.preimage f).hom (DeterminantSection.positiveDetCoefficient G))
                      (congrArg
                        (fun f : (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
                          (reductiveVariety G).toOver => f.left)
                        (selectedChart_singleton G F point a j)))))))


include hopen hdir hcF word q ha hgroup hco hn in
/-- The chosen two-stage coefficient extension retains its canonical evaluation
formula, full character cocycle, and degree-two determinant equations. -/
theorem exists_word_coefficient_evaluation [Finite J]
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (M.obj s)] [∀ s, Algebra.Smooth S (M.obj s)]
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      let MT := fixedFibreDiagram (R := T) (M := T) M
      ∃ (R' : Subalgebra ℤ K) (hTR : T ≤ R'),
        letI : Algebra T R' := (Subalgebra.inclusion hTR).toAlgebra
        letI : IsScalarTower T R' K := Subalgebra.inclusion.isScalarTower_right hTR K
        let N' := fixedFibreDiagram (R := R') (M := R') MT
        ∃ v' : N' ⋙ forget₂ (CommAlgCat R') CommRingCat ⟶
            F ⋙ forget₂ (CommAlgCat K) CommRingCat,
          T.FG ∧ R'.FG ∧
          (∀ s x, (v'.app s).hom x =
            (@scalarDiagramComparison.{u,u,u} K kField S T hST
            {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
              (@Subtype.preorder (Finset J)
                (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
                (fun s => s.Nonempty))) M F e) s
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R' K)
                (AlgHom.id T (MT.obj s)) x)) ∧
          (∀ s, Function.Injective (v'.app s).hom) ∧
          ∃ delta' : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
              (k : J) (_ : k ∈ s.val), (N'.obj s)ˣ,
            (∀ s j hj k hk, (v'.app s).hom (delta' s j hj k hk : N'.obj s) =
              (wordTransitionUnit G F beta s j hj k hk : F.obj s)) ∧
            (∀ s j hj k hk l hl,
              delta' s j hj l hl = delta' s k hk l hl * delta' s j hj k hk) ∧
            (∀ s t (f : s ⟶ t) j hj k hk,
              Units.map (N'.map f).hom.toMonoidHom (delta' s j hj k hk) =
                delta' t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
            ∃ P' : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N'.obj s),
              (∀ s, (P' s).natDegree ≤ 2 ∧
                Polynomial.map (v'.app s).hom (P' s) =
                  Polynomial.map (Spec.preimage (selectedFrame G F a s ≫
                    flagChartMap G (point (selectedIndex s))).left).hom
                      (DeterminantSection.simpleFramePolynomial G i
                        (DeterminantSection.positiveDetCoefficient G)) ∧
                (v'.app s).hom ((P' s).coeff 2) =
                  (Spec.preimage (selectedFrame G F a s ≫
                    flagChartMap G (point (selectedIndex s))).left).hom
                      (DeterminantSection.positiveDetCoefficient G) ∧
                ∀ n : ℕ, ((P' s) ^ n).coeff (2 * n) = ((P' s).coeff 2) ^ n) ∧
              (∀ j, (v'.app (singletonIndex j)).hom ((P' (singletonIndex j)).coeff 2) =
                wordRingCoefficient G F point a j) ∧
              ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
                (N'.map (singletonArrow s j hj)).hom ((P' (singletonIndex j)).coeff 2) =
                  (N'.map (singletonArrow s k hk)).hom ((P' (singletonIndex k)).coeff 2) *
                    (delta' s j hj k hk : N'.obj s) := by
  exact exists_indexed_stage
    (K := K) (J := J) (G := G) (F := F) (hopen := hopen) (hdir := hdir)
    (cF := cF) (hcF := hcF) (word := word) (q := q)
    (point := point) (a := a) (ha := ha) (beta := beta)
    (hgroup := hgroup) (hco := hco) (hn := hn)
    (i := i) (S := S) (hS := hS) (M := M) (e := e) (he := he)
    (hnatural := hnatural) (hbeta := hbeta)

end SchubertGeometry.RetainedCharacter
