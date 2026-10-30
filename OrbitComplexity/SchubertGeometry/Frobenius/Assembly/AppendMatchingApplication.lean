import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordCoefficients
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coordinates on a projective append atlas

The retained word section and both scalar extensions of the polynomial cover
are constructed together, preserving the original coefficient witnesses.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

open RetainedCharacter

universe u

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private coordinateScalarBase coordinateScalarMap fieldCoordinateCocone
  fieldCoordinateCocone_colimit fieldCoordinateDiagram_opens fieldCoordinateMap
  inverseCoordinates_affine retainedCoordinateRings retainedCoordinate_opens
  coefficientSectionResult retainedStageResult stageSectionResult
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels
open private map_exists_witness map_and_tail from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel
open private polynomial_chart_structure from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry

private theorem inverse_chart_base {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : A ⟶ D) (g : D ⟶ E) (h : B ⟶ E)
    (hf : f ≫ g = e.hom ≫ h) : (e.inv ≫ f) ≫ g = h := by
  rw [Category.assoc, hf, ← Category.assoc, e.inv_hom_id, Category.id_comp]

section Cover

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- Word coordinates with the polynomial and singleton covers on the same model. -/
def matchingWordCover
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    [(bsdhScheme G word).IsSeparated]
    (qK : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) (hW : ∀ j, IsAffine (W.X j))
    (V : Y.OpenCover.{u})
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j)))) : Prop :=
  let U := fun j => (W.f j).opensRange
  let hU : ∀ j, IsAffineOpen (U j) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let M := intersectionCoordinates base (intersectionOpens U)
  let F := intersectionCoordinates (bsdhToSpec G word) (inverseOpenDiagram qK (intersectionOpens U))
  let hEK := inverseCoordinates_affine base (bsdhToSpec G word) qK hK U hU
  let cF := fieldCoordinateCocone (bsdhToSpec G word) qK U hEK
  let hcF := fieldCoordinateCocone_colimit (bsdhToSpec G word) qK U
    W.iSup_opensRange hEK
  let q : cF.pt.left ⟶ bsdhScheme G word := 𝟙 _
  let hF := fieldCoordinateDiagram_opens base (bsdhToSpec G word) qK hK U hU
  letI : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  letI : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
    Scheme.forget).IsLocallyDirected := hF.2
  ∃ (point : W.I₀ → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset W.I₀ // s.Nonempty}) (j : W.I₀) (_ : j ∈ s.val)
      (k : W.I₀) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
    let laws := section_character_laws G F beta hnatural hbeta
    ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (F.obj s) k * fieldCoordinateMap base (bsdhToSpec G word) qK U s x) ∧
      (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom) ∧
      ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
        matchingRetainedResult G S base (bsdhToSpec G word) qK U cF hcF rfl word q
          point a ha beta hgroup laws.1 laws.2 i e V A eV T hST R hTR

variable (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    [(bsdhScheme G word).IsSeparated]
    (qK : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) [Finite W.I₀] (hW : ∀ j, IsAffine (W.X j))
    (V : Y.OpenCover.{u}) [Finite V.I₀]
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))


/-- Extend the given word-cover witnesses without changing their line or section. -/
theorem matching_word_cover_geometry
    (hV : ∀ j, ((eV j).inv ≫ V.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    (h : wordCoverModels G word i S base qK hK W hW) :
    matchingWordCover G word i S base qK hK W hW V A eV := by
  let hU : ∀ j, IsAffineOpen ((W.f j).opensRange) := fun j => by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  let hF := fieldCoordinateDiagram_opens base (bsdhToSpec G word) qK hK
    (fun j => (W.f j).opensRange) hU
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        ((intersectionCoordinates (bsdhToSpec G word)
          (inverseOpenDiagram qK (intersectionOpens (fun j => (W.f j).opensRange)))).map
              f).hom.toRingHom)) :=
    fun {_ _} f => hF.1 _ _ f
  let : ((((intersectionCoordinates (bsdhToSpec G word)
    (inverseOpenDiagram qK (intersectionOpens (fun j => (W.f j).opensRange)))).op ⋙ algSpec (.of K)
        ⋙
      Over.forget (Spec (.of K))) ⋙ Scheme.forget).IsLocallyDirected) := hF.2
  apply map_exists_witness h
  intro point h
  apply map_exists_witness h
  intro a h
  apply map_exists_witness h
  intro ha h
  apply map_exists_witness h
  intro beta h
  apply map_exists_witness h
  intro hgroup h
  apply map_exists_witness h
  intro hnatural h
  apply map_exists_witness h
  intro hbeta h
  apply map_exists_witness h
  intro e h
  refine ⟨h.1, h.2.1, ?_⟩
  apply map_exists_witness h.2.2
  intro T h
  apply map_exists_witness h
  intro hST h
  apply map_exists_witness h
  intro R h
  apply map_exists_witness h
  intro hTR h
  exact matching_retained_geometry G S base (bsdhToSpec G word) qK
    (fun j => (W.f j).opensRange)
    (fieldCoordinateCocone (bsdhToSpec G word) qK (fun j => (W.f j).opensRange)
      (inverseCoordinates_affine base (bsdhToSpec G word) qK hK
        (fun j => (W.f j).opensRange) (fun j => by
          let : IsAffine (W.X j) := hW j
          exact isAffineOpen_opensRange (W.f j))))
    (fieldCoordinateCocone_colimit (bsdhToSpec G word) qK
      (fun j => (W.f j).opensRange) W.iSup_opensRange
      (inverseCoordinates_affine base (bsdhToSpec G word) qK hK
        (fun j => (W.f j).opensRange) (fun j => by
          let : IsAffine (W.X j) := hW j
          exact isAffineOpen_opensRange (W.f j))))
    rfl word (𝟙 _) point a ha beta hgroup
    (section_character_laws G _ beta hnatural hbeta).1
    (section_character_laws G _ beta hnatural hbeta).2 i e
    (fun j => by
      let : IsAffine (W.X j) := hW j
      exact isAffineOpen_opensRange (W.f j))
    W.iSup_opensRange V A eV hV T hST R hTR h

end Cover

section Refinement

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) (S : Subalgebra ℤ K) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) (qY : bsdhScheme G word ⟶ Y)
    [(bsdhScheme G word).IsSeparated]
    (U : Y.OpenCover.{u})
    (A : U.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eU : ∀ j, U.X j ≅ Spec (.of (Polynomial (A j))))

/-- A scalar polynomial cover and retained word coordinates share one endpoint model. -/
def matchingWordStage (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  T.FG ∧ ∃ (YT : Scheme.{u}) (baseT : YT ⟶ Spec (.of T))
    (qT : YT ⟶ Y) (mT : bsdhScheme G word ⟶ YT)
    (hproper : IsProper baseT) (hsmooth : Smooth baseT)
    (_hTcart : IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hKcart : IsPullback mT (bsdhToSpec G word) baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K)))),
    mT ≫ qT = qY ∧
    ∃ (W : YT.OpenCover.{u}) (hfiniteW : Finite W.I₀) (haffW : ∀ j, IsAffine (W.X j)),
    let : Finite W.I₀ := hfiniteW
    let : IsProper baseT := hproper
    let : Smooth baseT := hsmooth
    ∃ (V : YT.OpenCover.{u}) (hfiniteV : Finite V.I₀)
      (haffV : ∀ j, IsAffine (V.X j)) (index : V.I₀ ≃ U.I₀)
      (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (T ⊗[S] A (index j))))),
      let : Finite V.I₀ := hfiniteV
      let : ∀ j, IsAffine (V.X j) := haffV
      (∀ j, IsPullback
        ((eV j).hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A (index j) →ₐ[S]
            T ⊗[S] A (index j)).toRingHom)))
        (V.f j) ((eU (index j)).inv ≫ U.f (index j)) qT) ∧
      (∀ j, V.f j ≫ baseT = (eV j).hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap T (Polynomial (T ⊗[S] A (index j)))))) ∧
      (∀ j, V.f j ≫ qT = (eV j).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight : A (index j) →ₐ[S]
            T ⊗[S] A (index j)).toRingHom)) ≫
          (eU (index j)).inv ≫ U.f (index j)) ∧
      matchingWordCover G word i T baseT mT hKcart W haffW V
        (fun j => T ⊗[S] A (index j)) eV

variable [Finite U.I₀]

/-- Construct the scalar polynomial cover using the prescribed endpoint comparisons. -/
theorem matching_word_stage_geometry
    (hU : ∀ j, ((eU j).inv ≫ U.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (h : wordCoverStage G word i S base qY T hST) :
    matchingWordStage G word i S base qY U A eU T hST := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  obtain ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart,
    hmT, W, hfiniteW, haffW, hmodels⟩ := h
  let : Finite W.I₀ := hfiniteW
  let : IsProper baseT := hproper
  let : Smooth baseT := hsmooth
  obtain ⟨V, hfiniteV, haffV, index, eV, hVcart, hVbase, hVold⟩ :=
    exists_append_scalar_cover base baseT qT hTcart U A eU hU
  let : Finite V.I₀ := hfiniteV
  refine ⟨hT, YT, baseT, qT, mT, hproper, hsmooth, hTcart, hKcart,
    hmT, W, hfiniteW, haffW, V, hfiniteV, haffV, index, eV,
    hVcart, hVbase, hVold, ?_⟩
  exact matching_word_cover_geometry G word i T baseT mT hKcart W haffW
    V (fun j => T ⊗[S] A (index j)) eV
    (fun j => inverse_chart_base (eV j) (V.f j) baseT _ (hVbase j)) hmodels

end Refinement


section Atlas

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (R : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)

/-- A projective append atlas together with a retained character line, common affine covers and all
determinant-section powers on a scalar extension of that same append model. -/
def matchingAppendAtlas : Prop :=
  letI := wordSchemeSeparated G (word ++ [i])
  let scale := fun s j hj k hk ↦
    Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  ∃ (c₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val), N.obj s),
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] (c₀ s j hj k hk : N.obj s)) =
      (scale s j hj k hk : F.obj s)) ∧
    (∀ s j hj k hk, e s ((1 : K) ⊗ₜ[R] a₀ s j hj k hk) = shift s j hj k hk) ∧
    (∀ s j hj k hk l hl, c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk ∧
      a₀ s j hj l hl = (c₀ s k hk l hl : N.obj s) * a₀ s j hj k hk + a₀ s k hk l hl) ∧
    (∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c₀ s j hj k hk) =
        c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a₀ s j hj k hk) = a₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
    ∃ (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
      (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
      (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))),
      (∀ s, π.app (op s) = (eP s).hom ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2))) ∧
      (∀ s t (f : s ⟶ t), D.map f.op ≫ (eP s).hom = (eP t).hom ≫
        (projectiveLineScalingIso
          (c₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        (projectiveLineTranslationIso
          (a₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom) ∧
      π.Equifibered ∧ ∃ (cD : Cocone D) (q : cD.pt ⟶ cG.pt.left),
        Nonempty (IsColimit cD) ∧
        (∀ s, cD.ι.app s ≫ q = π.app s ≫ (cG.ι.app s).left) ∧
        (∀ s, IsPullback (π.app s) (cD.ι.app s) (cG.ι.app s).left q) ∧
        IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
        ∃ (hOpen : ∀ s, IsOpenImmersion (cD.ι.app s))
          (hCover : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
            ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
              (pullback.fst f (cD.ι.app s)) z = y),
        ∃ m : bsdhScheme G (word ++ [i]) ⟶ cD.pt,
          IsPullback m (bsdhToSpec G (word ++ [i])) (q ≫ cG.pt.hom)
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
          IsPullback m (bsdhAppendFst G word i) q m₀ ∧
          (∀ s, projectiveAppendChart G i (F.obj s)
              (p s (sel s).val (sel s).property) (c (sel s).val) ≫ m =
            projectiveCoeffMap (ULift.{u} (Fin 2))
              ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
                (eP s).inv ≫ cD.ι.app (op s)) ∧
          (∀ s (j : ULift.{u} (Fin 2)),
            (projectiveLinePolynomialChart (F.obj s) j ≫
                projectiveAppendChart G i (F.obj s)
                  (p s (sel s).val (sel s).property) (c (sel s).val)) ≫ m =
              Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
                ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) ≫
                (projectiveLinePolynomialChart (N.obj s) j ≫
                  (eP s).inv ≫ cD.ι.app (op s)) ∧
            (projectiveLinePolynomialChart (N.obj s) j ≫
                (eP s).inv ≫ cD.ι.app (op s)) ≫ q =
              Spec.map (CommRingCat.ofHom (Polynomial.C : N.obj s →+* Polynomial (N.obj s))) ≫
                (cG.ι.app (op s)).left ∧
            (projectiveLinePolynomialChart (F.obj s) j ≫
                projectiveAppendChart G i (F.obj s)
                  (p s (sel s).val (sel s).property) (c (sel s).val)) ≫
                  bsdhAppendFst G word i =
              Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫
                b.app (op s)) ∧
          ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T),
            matchingWordStage G (word ++ [i]) i R
              (q ≫ cG.pt.hom) m
              (appendPolynomialCover N D eP cD hOpen hCover)
              (fun j => N.obj j.1)
              (fun j => Iso.refl (Spec (.of (Polynomial (N.obj j.1))))) T hRT


private theorem expose_two {P Q R : Prop} {Z : P → Q → Prop}
    (h : P ∧ Q ∧ R) (f : ∀ hp hq, R → Z hp hq) :
    ∃ hp hq, Z hp hq := ⟨h.1, h.2.1, f h.1 h.2.1 h.2.2⟩

/-- Extend the polynomial atlas by matching coordinates using its given cocone. -/
theorem matching_append_atlas [finiteJ : Finite J]
    (h : appendWordAtlasSpec R G word i V₀ F N e p c beta sel b cG m₀) :
    matchingAppendAtlas R G word i V₀ F N e p c beta sel b cG m₀ := by
  let := wordSchemeSeparated G (word ++ [i])
  apply map_exists_witness h
  intro c₀ h
  apply map_exists_witness h
  intro a₀ h
  apply map_and_tail h
  intro hc₀ h
  apply map_and_tail h
  intro ha₀ h
  apply map_and_tail h
  intro hcocycle h
  apply map_and_tail h
  intro hnatural h
  apply map_exists_witness h
  intro D h
  apply map_exists_witness h
  intro eP h
  apply map_exists_witness h
  intro π h
  apply map_and_tail h
  intro hπ h
  apply map_and_tail h
  intro hD h
  apply map_and_tail h
  intro hπcart h
  apply map_exists_witness h
  intro cD h
  apply map_exists_witness h
  intro q h
  apply map_and_tail h
  intro hcD h
  apply map_and_tail h
  intro hqlegs h
  apply map_and_tail h
  intro hqcart h
  apply map_and_tail h
  intro hqproper h
  apply map_and_tail h
  intro hqsmooth h
  apply map_and_tail h
  intro hqconnected h
  apply expose_two h
  intro hOpen hCover h
  apply map_exists_witness h
  intro m h
  apply map_and_tail h
  intro hmcart h
  apply map_and_tail h
  intro hmappend h
  apply map_and_tail h
  intro hprojective h
  apply map_and_tail h
  intro hpolynomial h
  apply map_exists_witness h
  intro T h
  apply map_exists_witness h
  intro hRT h
  let V := appendPolynomialCover N D eP cD hOpen hCover
  let A : V.I₀ → Type u := fun j => N.obj j.1
  let eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))) :=
    fun j => Iso.refl (Spec (.of (Polynomial (A j))))
  have hV : ∀ j, ((eV j).inv ≫ V.f j) ≫ (q ≫ cG.pt.hom) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (A j)))) := fun j => by
    have hproj := appendPolynomialCover_projection N D eP cD hOpen hCover
      cG q π hπ hqlegs j.1 j.2
    exact polynomial_chart_structure (V.f j) q cG.pt.hom
      (cG.ι.app (op j.1)).left hproj (cG.ι.app (op j.1)).w
  exact matching_word_stage_geometry G (word ++ [i]) i R (q ≫ cG.pt.hom) m
    V A eV hV T hRT h



/-- The original coefficient extension with its atlas and matching coordinates. -/
def appendMatchingApplicationSpec (T : Subalgebra ℤ K) (hRT : R ≤ T) : Prop :=
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  let NT := fixedFibreDiagram (R := T) (M := T) N
  let eT := @scalarDiagramComparison.{u,u,u} K kField R T hRT
    {s : Finset J // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) N F e
  (∀ {s t} (f : s ⟶ t), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (NT.map f).hom.toRingHom))) ∧
  ((NT.op ⋙ algSpec (.of T) ⋙ Over.forget (Spec (.of T))) ⋙
    Scheme.forget).IsLocallyDirected ∧
  (∀ s t (f : s ⟶ t), (eT t).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (NT.map f).hom) =
      (F.map f).hom.comp (eT s).toAlgHom) ∧
  ∃ (cT : Cocone (NT.op ⋙ algSpec (.of T))) (qT : cT.pt.left ⟶ cG.pt.left),
    Nonempty (IsColimit cT) ∧
    IsPullback qT cT.pt.hom cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) ∧
    (∀ s, (cT.ι.app (op s)).left ≫ qT =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj s →ₐ[R] T ⊗[R] N.obj s).toRingHom) ≫
          (cG.ι.app (op s)).left) ∧
    ∃ mT : bsdhScheme G word ⟶ cT.pt.left,
      IsPullback mT (bsdhToSpec G word) cT.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
      mT ≫ qT = m₀ ∧
      (∀ s, b.app (op s) ≫ mT =
        Spec.map (CommRingCat.ofHom
          ((eT s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
            (cT.ι.app (op s)).left) ∧
      matchingAppendAtlas T G word i V₀ F NT eT p c beta sel b cT mT


/-- Construct the matching-cover comparison on the same retained coefficient stage. -/
theorem append_matching_application [finiteJ : Finite J]
    (T : Subalgebra ℤ K) (hRT : R ≤ T)
    (h : extendedAppendWordSpec R G word i V₀ F N e p c beta sel b cG m₀ T hRT) :
    appendMatchingApplicationSpec R G word i V₀ F N e p c beta sel b cG m₀ T hRT := by
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  apply map_and_tail h
  intro hopen h
  apply map_and_tail h
  intro hdir h
  apply map_and_tail h
  intro he h
  apply map_exists_witness h
  intro cT h
  apply map_exists_witness h
  intro qT h
  apply map_and_tail h
  intro hcT h
  apply map_and_tail h
  intro hcart h
  apply map_and_tail h
  intro hlegs h
  apply map_exists_witness h
  intro mT h
  apply map_and_tail h
  intro hmcart h
  apply map_and_tail h
  intro hmold h
  apply map_and_tail h
  intro hmlegs h
  exact matching_append_atlas T G word i V₀ F
    (fixedFibreDiagram (R := T) (M := T) N)
    (@scalarDiagramComparison.{u,u,u} K kField R T hRT
    {s : Finset J // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty})) N F e)
    p c beta sel b cT mT h

end Atlas

/-- One coefficient extension retains the append coefficients and constructs
the matching-model refinement from the same atlas and word-section witnesses. -/
theorem exists_append_matching_application {K : Type u}
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
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
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
    (hbbase : ∀ s, b.app (op s) ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hcart : ∀ s, IsPullback
      (fst ((algSpec (.of K)).obj (op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (op s)) (bsdhAppendFst G word i))
    (cG : Cocone (N.op ⋙ algSpec (.of S)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hbmodel : ∀ s, b.app (op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (op s)).left)
    [finiteJ : Finite J]
    [nodeFP : ∀ s, Algebra.FinitePresentation S (N.obj s)]
    [nodeSmooth : ∀ s, Algebra.Smooth S (N.obj s)]
    [baseProper : IsProper cG.pt.hom] [baseSmooth : Smooth cG.pt.hom]
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
      T.FG ∧ appendMatchingApplicationSpec S G word i V₀ F N e p c beta sel b cG m₀
        T hST ∧ appendCoefficientSpec (R := T) N F e delta P := by
  have h := @exists_append_word_coefficients.{u} K kField kClosed kZero S hS
    G word i J V₀ F N e he fOpen fDir nOpen nDir p c hpn beta
    hchart hnatural hbeta sel b hb hbbase hcart cG m₀ hm₀ hbmodel
    finiteJ nodeFP nodeSmooth baseProper baseSmooth delta hco hn P hP hr hcG
  apply map_exists_witness h
  intro T h
  apply map_exists_witness h
  intro hST h
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  exact ⟨h.1, append_matching_application S G word i V₀ F N e p c beta sel b cG m₀
    T hST h.2.1, h.2.2⟩

end SchubertGeometry
