import OrbitComplexity.SchubertGeometry.Normality.Bundles.AppendPolynomialCover
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Character lines on projective append models

The finite polynomial atlas of an append model determines a retained
word character line and all powers of its determinant section on a scalar
extension of the same model.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

universe u

open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels

private theorem append_word_cover {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (R : Subalgebra ℤ K) (hR : R.FG) {I : Type u} [Finite I]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (ho : ∀ s, IsOpenImmersion (cD.ι.app s))
    (hc : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
      ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
        (pullback.fst f (cD.ι.app s)) z = y)
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    [IsProper cG.pt.hom] [Smooth cG.pt.hom]
    (q : cD.pt ⟶ cG.pt.left) [IsProper q] [Smooth q]
    (m : bsdhScheme G (word ++ [i]) ⟶ cD.pt)
    (hm : IsPullback m (bsdhToSpec G (word ++ [i])) (q ≫ cG.pt.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    letI := wordSchemeSeparated G (word ++ [i])
    ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T),
      RetainedCharacter.wordCoverStage G (word ++ [i]) i R
        (q ≫ cG.pt.hom) m T hRT := by
  let := wordSchemeSeparated G (word ++ [i])
  let U := appendPolynomialCover N D eP cD ho hc
  let : IsProper (q ≫ cG.pt.hom) := inferInstance
  let : Smooth (q ≫ cG.pt.hom) := inferInstance
  exact RetainedCharacter.exists_word_cover_models G (word ++ [i]) i R hR
    (q ≫ cG.pt.hom) m hm U (fun j => inferInstance)

private theorem map_exists_witness {A : Sort*} {P Q : A → Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q a) : ∃ a, Q a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, f a ha⟩

private theorem map_and_tail {P Q R : Prop}
    (h : P ∧ Q) (f : P → Q → R) : P ∧ R := ⟨h.1, f h.1 h.2⟩

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

/-- A projective append atlas together with a retained character line and all
determinant-section powers on a scalar extension of that same append model. -/
def appendWordAtlasSpec : Prop :=
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
        (∀ s, IsOpenImmersion (cD.ι.app s)) ∧
        (∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
          ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
            (pullback.fst f (cD.ι.app s)) z = y) ∧
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
            RetainedCharacter.wordCoverStage G (word ++ [i]) i R
              (q ≫ cG.pt.hom) m T hRT

private theorem append_atlas_word [finiteJ : Finite J] (hR : R.FG)
    [baseProper : IsProper cG.pt.hom] [baseSmooth : Smooth cG.pt.hom]
    (h : appendAtlasSpec G word i V₀ F N e p c beta sel b cG m₀) :
    appendWordAtlasSpec R G word i V₀ F N e p c beta sel b cG m₀ := by
  let := wordSchemeSeparated G (word ++ [i])
  unfold appendAtlasSpec at h
  unfold appendWordAtlasSpec
  apply map_exists_witness h
  intro c₀ h
  apply map_exists_witness h
  intro a₀ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_exists_witness h
  intro D h
  apply map_exists_witness h
  intro eP h
  apply map_exists_witness h
  intro π h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_exists_witness h
  intro cD h
  apply map_exists_witness h
  intro q h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro hproper h
  apply map_and_tail h
  intro hsmooth h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro hopen h
  apply map_and_tail h
  intro hcover h
  apply map_exists_witness h
  intro m h
  apply map_and_tail h
  intro hm h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ hpoly
  let : IsProper q := hproper
  let : Smooth q := hsmooth
  exact ⟨hpoly, append_word_cover G word i R hR N D eP cD hopen hcover cG q m hm⟩

/-- The prior coefficient diagram, its old projections and its append atlas
are retained together with the next word character line and section. -/
def extendedAppendWordSpec (T : Subalgebra ℤ K) (hRT : R ≤ T) : Prop :=
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
      appendWordAtlasSpec T G word i V₀ F NT eT p c beta sel b cT mT

private theorem extended_atlas_word [finiteJ : Finite J]
    [baseProper : IsProper cG.pt.hom] [baseSmooth : Smooth cG.pt.hom]
    (T : Subalgebra ℤ K) (hRT : R ≤ T) (hT : T.FG)
    (h : let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
      let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
      extendedAppendAtlasSpec (T := T) G word i V₀ F N e p c beta sel b cG m₀ hRT) :
    extendedAppendWordSpec R G word i V₀ F N e p c beta sel b cG m₀ T hRT := by
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  unfold extendedAppendAtlasSpec at h
  unfold extendedAppendWordSpec
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_exists_witness h
  intro cT h
  apply map_exists_witness h
  intro qT h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro hcart h
  apply map_and_tail h
  intro _ h
  apply map_exists_witness h
  intro mT h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  apply map_and_tail h
  intro _ h
  let : IsProper cT.pt.hom := MorphismProperty.of_isPullback (P := @IsProper) hcart inferInstance
  let : Smooth cT.pt.hom := MorphismProperty.of_isPullback (P := @Smooth) hcart inferInstance
  exact append_atlas_word T G word i V₀ F _ _ p c beta sel b cT mT hT h

end Atlas

end SchubertGeometry
