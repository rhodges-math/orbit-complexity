import OrbitComplexity.SchubertGeometry.Normality.Transitions.BorelAppendCharts
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ChosenProperBundle
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retaining the append atlas on a fixed prior diagram

The coefficient extension preserves the given prior cocone. Its projective
append charts and their comparison maps are constructed from the retained
Borel transition coefficients.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

open private chosen_parameters parameterSpec bundle_of_parameters from
  OrbitComplexity.SchubertGeometry.Normality.Bundles.ChosenProperBundle

private theorem coefficient_base_factor {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K] :
    Spec.map (CommRingCat.ofHom (algebraMap S K)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S R)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : S →+* K ↦ Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq S R K)

private theorem comparison_lift {B T Z X P Y : Scheme.{u}}
    (κ : T ⟶ B) (ell : Z ⟶ T) (oldBase : Z ⟶ B) (hμ : oldBase = ell ≫ κ)
    (fX : X ⟶ B) (fP : P ⟶ T) (q : P ⟶ X)
    (hq : IsPullback q fP fX κ) (fY : Y ⟶ Z) (m₀ : Y ⟶ X)
    (h₀ : IsPullback m₀ fY fX oldBase) :
    ∃ m : Y ⟶ P, m ≫ q = m₀ ∧ m ≫ fP = fY ≫ ell ∧
      IsPullback m fY fP ell := by
  have h₁ : IsPullback m₀ fY fX (ell ≫ κ) := by simpa only [← hμ] using h₀
  let m := hq.lift m₀ (fY ≫ ell) (by rw [h₁.w, Category.assoc])
  exact ⟨m, hq.lift_fst _ _ _, hq.lift_snd _ _ _, h₁.of_right' hq⟩

private theorem chart_comparison {B T X P W Z V Y : Scheme.{u}}
    (κ : T ⟶ B) (fX : X ⟶ B) (fP : P ⟶ T) (q : P ⟶ X)
    (hq : IsPullback q fP fX κ) (m : Y ⟶ P) (m₀ : Y ⟶ X)
    (hm : m ≫ q = m₀) (b : W ⟶ Y) (a : W ⟶ Z) (a₀ : W ⟶ V)
    (r : Z ⟶ V) (g : Z ⟶ P) (g₀ : V ⟶ X)
    (hb : b ≫ m₀ = a₀ ≫ g₀) (hg : g ≫ q = r ≫ g₀)
    (ha : a ≫ r = a₀) (hbase : (b ≫ m) ≫ fP = (a ≫ g) ≫ fP) :
    b ≫ m = a ≫ g := by
  apply hq.hom_ext
  · calc
      (b ≫ m) ≫ q = b ≫ m₀ := by rw [Category.assoc, hm]
      _ = a₀ ≫ g₀ := hb
      _ = (a ≫ g) ≫ q := by rw [Category.assoc, hg, ← Category.assoc, ha]
  · exact hbase

private theorem tensor_coordinate_factor {S R K A B : Type u}
    [CommRing S] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S A] [Algebra K B]
    (e : K ⊗[S] A ≃ₐ[K] B) :
    (((Algebra.TensorProduct.cancelBaseChange S R K K A).trans e).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom).comp
          (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
      e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
  ext a
  change e (Algebra.TensorProduct.cancelBaseChange S R K K A
      ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] a))) = e ((1 : K) ⊗ₜ[S] a)
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

private theorem tensor_coordinate_spec {K : Type u} [kField : Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    {J : Type u} [jCat : Category J]
    (N : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ j, K ⊗[S] N.obj j ≃ₐ[K] F.obj j) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    ∀ j, Spec.map (CommRingCat.ofHom
        ((@scalarDiagramComparison.{u,u,u} K kField S R hSR J jCat N F e j).toRingHom.comp
          Algebra.TensorProduct.includeRight.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj j →ₐ[S] R ⊗[S] N.obj j).toRingHom) =
      Spec.map (CommRingCat.ofHom
        ((e j).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  intro j
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f : N.obj j →+* F.obj j => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  change (@scalarDiagramComparison.{u,u,u} K kField S R hSR J jCat N F e j)
    ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x)) = e j ((1 : K) ⊗ₜ[S] x)
  rw [@scalarDiagramComparison_tmul.{u,u,u} K kField S R hSR J jCat N F e j]
  simp only [map_one, one_mul]

private theorem tensor_coordinate_base {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B] [Algebra R B]
    [IsScalarTower R K B] (e : K ⊗[R] A ≃ₐ[K] B) :
    Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f : R →+* B ↦ Spec.map (CommRingCat.ofHom f))
  exact (tensorImageHom e).comp_algebraMap.trans (IsScalarTower.algebraMap_eq R K B)

private theorem scalar_prior_comparison {K : Type u} [kField : Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    {J : Type u} [jCat : Category J]
    (N : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    ∀ (cG : Cocone (N.op ⋙ algSpec (.of S)))
    (cR : Cocone ((fixedFibreDiagram (R := R) (M := R) N).op ⋙ algSpec (.of R)))
    (q : cR.pt.left ⟶ cG.pt.left)
    (_hq : IsPullback q cR.pt.hom cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (_hlegs : ∀ s, (cR.ι.app (.op s)).left ≫ q =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj s →ₐ[S] R ⊗[S] N.obj s).toRingHom) ≫
          (cG.ι.app (.op s)).left)
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of K))
    (b : ∀ s, Spec (.of (F.obj s)) ⟶ Y) (m₀ : Y ⟶ cG.pt.left)
    (_h₀ : IsPullback m₀ base cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (_hbbase : ∀ s, b s ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (_hbmodel : ∀ s, b s ≫ m₀ = Spec.map (CommRingCat.ofHom
      ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
        (cG.ι.app (.op s)).left),
    let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR J jCat N F e
    ∃ m : Y ⟶ cR.pt.left,
      IsPullback m base cR.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      m ≫ q = m₀ ∧
      ∀ s, b s ≫ m = Spec.map (CommRingCat.ofHom
        ((eR s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cR.ι.app (.op s)).left := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  intro cG cR q hq hlegs Y base b m₀ h₀ hbbase hbmodel eR
  obtain ⟨m, hmq, hmb, hcart⟩ := comparison_lift _ _ _ coefficient_base_factor
    cG.pt.hom cR.pt.hom q hq base m₀ h₀
  refine ⟨m, hcart, hmq, ?_⟩
  intro s
  apply chart_comparison _ _ _ q hq m m₀ hmq (b s) _ _ _ _ _ (hbmodel s)
    (hlegs s) (@tensor_coordinate_spec.{u} K kField S R hSR J jCat N F e s)
  calc
    (b s ≫ m) ≫ cR.pt.hom = (b s ≫ base) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [Category.assoc, hmb, ← Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by rw [hbbase]
    _ = _ := by
      let a : Spec (.of (F.obj s)) ⟶
          (((fixedFibreDiagram (R := R) (M := R) N).op ⋙
            algSpec (.of R)).obj (.op s)).left :=
        Spec.map (CommRingCat.ofHom
          ((eR s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
      have ha : a ≫ (((fixedFibreDiagram (R := R) (M := R) N).op ⋙
          algSpec (.of R)).obj (.op s)).hom =
          Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
        tensor_coordinate_base (eR s)
      have hleg := (cR.ι.app (.op s)).w
      exact ha.symm.trans ((congrArg (fun g ↦ a ≫ g) hleg.symm).trans
        (Category.assoc a (cR.ι.app (.op s)).left cR.pt.hom).symm)

section Atlas

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {R : Subalgebra ℤ K} (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    [nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirN : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
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
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hbmodel : ∀ s, b.app (.op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left)


/-- The projective append atlas, with its two polynomial charts and both projection maps. -/
def appendAtlasSpec : Prop :=
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
        (eP : ∀ s, D.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
        (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))),
        (∀ s, π.app (.op s) = (eP s).hom ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2))) ∧
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
            ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}), (pullback.fst f (cD.ι.app s)) z = y)
                ∧
          ∃ m : bsdhScheme G (word ++ [i]) ⟶ cD.pt,
            IsPullback m (bsdhToSpec G (word ++ [i])) (q ≫ cG.pt.hom)
              (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
            IsPullback m (bsdhAppendFst G word i) q m₀ ∧
            (∀ s, projectiveAppendChart G i (F.obj s)
                (p s (sel s).val (sel s).property) (c (sel s).val) ≫ m =
              projectiveCoeffMap (ULift.{u} (Fin 2))
                ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
                  (eP s).inv ≫ cD.ι.app (.op s)) ∧
            ∀ s (j : ULift.{u} (Fin 2)),
              (projectiveLinePolynomialChart (F.obj s) j ≫
                  projectiveAppendChart G i (F.obj s)
                    (p s (sel s).val (sel s).property) (c (sel s).val)) ≫ m =
                Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
                  ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) ≫
                  (projectiveLinePolynomialChart (N.obj s) j ≫
                    (eP s).inv ≫ cD.ι.app (.op s)) ∧
              (projectiveLinePolynomialChart (N.obj s) j ≫
                  (eP s).inv ≫ cD.ι.app (.op s)) ≫ q =
                Spec.map (CommRingCat.ofHom (Polynomial.C : N.obj s →+* Polynomial (N.obj s))) ≫
                  (cG.ι.app (.op s)).left ∧
              (projectiveLinePolynomialChart (F.obj s) j ≫
                  projectiveAppendChart G i (F.obj s)
                    (p s (sel s).val (sel s).property) (c (sel s).val)) ≫
                    bsdhAppendFst G word i =
                Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫
                  b.app (.op s)

/-- Scalar extension of the prescribed prior diagram and its append atlas. -/
def extendedAppendAtlasSpec {T : Subalgebra ℤ K} (hRT : R ≤ T) : Prop :=
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  let NT := fixedFibreDiagram (R := T) (M := T) N
  let eT := @scalarDiagramComparison.{u,u,u} K kField R T hRT
    {s : Finset J // s.Nonempty}
    (@Preorder.smallCategory {s : Finset J // s.Nonempty}
      (@Subtype.preorder (Finset J)
        (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
        (fun s => s.Nonempty))) N F e
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
    (∀ s, (cT.ι.app (.op s)).left ≫ qT =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj s →ₐ[R] T ⊗[R] N.obj s).toRingHom) ≫
          (cG.ι.app (.op s)).left) ∧
    ∃ mT : bsdhScheme G word ⟶ cT.pt.left,
      IsPullback mT (bsdhToSpec G word) cT.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
      mT ≫ qT = m₀ ∧
      (∀ s, b.app (.op s) ≫ mT =
        Spec.map (CommRingCat.ofHom
          ((eT s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
            (cT.ι.app (.op s)).left) ∧
      appendAtlasSpec G word i V₀ F NT eT p c beta sel b cT mT

include hpn hchart hnatural hbeta b hb hbbase hcart hm₀ hbmodel

private theorem atlas_after_scalar_extension {T : Subalgebra ℤ K} (hRT : R ≤ T)
    (hcG : IsColimit cG) :
    letI : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
    letI : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
    let scale := fun s j hj k hk ↦
      Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
    let NT := fixedFibreDiagram (R := T) (M := T) N
    let eT := @scalarDiagramComparison.{u,u,u} K kField R T hRT
      {s : Finset J // s.Nonempty}
      (@Preorder.smallCategory {s : Finset J // s.Nonempty}
        (@Subtype.preorder (Finset J)
          (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
          (fun s => s.Nonempty))) N F e
    (∀ s t (f : s ⟶ t), (eT t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (NT.map f).hom) =
        (F.map f).hom.comp (eT s).toAlgHom) →
    modelProjectiveSpec NT F eT sel scale shift →
    extendedAppendAtlasSpec (T := T) G word i V₀ F N e p c beta sel b cG m₀ hRT := by
  let : Algebra R T := (Subalgebra.inclusion hRT).toAlgebra
  let : IsScalarTower R T K := Subalgebra.inclusion.isScalarTower_right hRT K
  intro scale shift NT eT heT H
  let : ∀ {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t),
      IsOpenImmersion (((N.op ⋙ algSpec (.of R)).map f).left) := fun f ↦
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let : (((N.op ⋙ algSpec (.of R)) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := hdirN
  obtain ⟨hopenT, hdirT, cT, qT, hcT, hqT, hlegs⟩ :=
    exists_fixed_scalar_cocone (R := T) N cG hcG
  let ntOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (NT.map f).hom.toRingHom)) := fun f ↦ hopenT f.op
  let ntDir : ((NT.op ⋙ algSpec (.of T) ⋙ Over.forget (Spec (.of T))) ⋙
      Scheme.forget).IsLocallyDirected := hdirT
  obtain ⟨mT, hmT, hmproj, hmchart⟩ := @scalar_prior_comparison.{u} K kField R T hRT
    {s : Finset J // s.Nonempty}
    (@Preorder.smallCategory {s : Finset J // s.Nonempty}
      (@Subtype.preorder (Finset J)
        (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J))
        (fun s => s.Nonempty))) N F e cG cT qT hqT
    (fun s ↦ hlegs (.op s)) (bsdhScheme G word) (bsdhToSpec G word)
    (fun s ↦ b.app (.op s)) m₀ hm₀ hbbase hbmodel
  refine ⟨(fun f ↦ hopenT f.op), hdirT, heT, cT, qT, hcT, hqT,
    (fun s ↦ hlegs (.op s)), mT, hmT, hmproj, hmchart, ?_⟩
  obtain ⟨hcT⟩ := hcT
  exact @borel_append_polynomial_charts.{u} K T kField kClosed kZero inferInstance inferInstance
    G word i J V₀ F NT eT heT fOpen fDir ntOpen ntDir p c hpn beta hchart
    hnatural hbeta sel b hb hbbase hcart cT mT hmT hmchart
    (bundle_of_parameters NT F eT sel scale shift cT hcT H)


end Atlas

/-- Borel transition coefficients produce the append atlas after a coefficient
extension of the prescribed prior cocone, retaining its comparison projection. -/
theorem exists_retained_append_atlas {K : Type u}
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
    (hcG : IsColimit cG) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ extendedAppendAtlasSpec (T := T) G word i V₀ F N e p c beta sel b cG m₀ hST := by
  have H := chosen_parameters G i S hS N F e he sel beta hnatural hbeta
  obtain ⟨T, hST, H⟩ := H
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  obtain ⟨hT, heT, hparams⟩ := H
  refine ⟨T, hST, hT, ?_⟩
  exact atlas_after_scalar_extension G word i V₀ F N e p c hpn beta hchart hnatural hbeta
    sel b hb hbbase hcart cG m₀ hm₀ hbmodel hST hcG heT hparams

end SchubertGeometry
