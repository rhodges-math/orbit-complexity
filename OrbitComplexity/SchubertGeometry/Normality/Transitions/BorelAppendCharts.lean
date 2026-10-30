import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.BorelAppendModel
import OrbitComplexity.SchubertGeometry.Normality.Models.IntegralProjectiveCoeff

/-! # Both polynomial charts of the same retained arithmetic append -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open FrobeniusSplitting CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
noncomputable section
universe u
namespace SchubertGeometry

private theorem polynomial_chart_base_post (A : Type u) [CommRing A]
    (j : ULift.{u} (Fin 2)) {Y : Scheme.{u}} (g : Spec (.of A) ⟶ Y) :
    projectiveLinePolynomialChart A j ≫ projectiveToSpec A (ULift.{u} (Fin 2)) ≫ g =
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ g :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ g) (projectiveLinePolynomialChart_base A j))

private theorem polynomial_chart_projection (A : Type u) [CommRing A]
    (j : ULift.{u} (Fin 2)) {X Y : Scheme.{u}}
    (f : projectiveScheme A (ULift.{u} (Fin 2)) ⟶ X) (q : X ⟶ Y)
    (g : Spec (.of A) ⟶ Y)
    (h : projectiveToSpec A (ULift.{u} (Fin 2)) ≫ g = f ≫ q) :
    (projectiveLinePolynomialChart A j ≫ f) ≫ q =
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ g := by
  calc
    (projectiveLinePolynomialChart A j ≫ f) ≫ q =
      projectiveLinePolynomialChart A j ≫ (f ≫ q) := Category.assoc _ _ _
    _ = projectiveLinePolynomialChart A j ≫
        (projectiveToSpec A (ULift.{u} (Fin 2)) ≫ g) :=
      congrArg (fun z ↦ projectiveLinePolynomialChart A j ≫ z) h.symm
    _ = _ := polynomial_chart_base_post A j g

private theorem polynomial_chart_iso_projection (A : Type u) [CommRing A]
    (j : ULift.{u} (Fin 2)) {P X Y : Scheme.{u}}
    (eP : P ≅ projectiveScheme A (ULift.{u} (Fin 2)))
    (π : P ⟶ Spec (.of A)) (leg : P ⟶ X) (q : X ⟶ Y) (g : Spec (.of A) ⟶ Y)
    (hπ : π = eP.hom ≫ projectiveToSpec A (ULift.{u} (Fin 2)))
    (hq : leg ≫ q = π ≫ g) :
    (projectiveLinePolynomialChart A j ≫ eP.inv ≫ leg) ≫ q =
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ g := by
  apply polynomial_chart_projection A j (eP.inv ≫ leg) q g
  rw [Category.assoc, hq, hπ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {K R : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K] [rComm :
  CommRing R]
    [rKAlg : Algebra R K] (G : ReductiveGroupData K) (word : List G.rootBase.support)
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
    [nDir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
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


include he hpn hchart hnatural hbeta b hb hbbase hcart hm₀ hbmodel

/-- The append constructor retains both polynomial chart maps, their
scalar comparison and the two original append-projection equations. -/
theorem borel_append_polynomial_charts :
    let scale := fun s j hj k hk ↦
      Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
    modelBundleSpec N F e sel scale shift cG →
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
                  b.app (.op s) := by
  intro scale shift hBundle
  obtain ⟨c₀, a₀, hc₀, ha₀, hco, hn, D, eP, π, hproj, hmap, hπ,
    cD, q, hD, hq, hcartD, hproper, hsmooth, hgc, hopen, hcoverage, m, hm, hmq, hlegs⟩ :=
    @borel_append_comparison.{u} K R kField kClosed kZero rComm rKAlg
      G word i J V₀ F N e he fOpen fDir nOpen nDir p c hpn beta hchart hnatural hbeta sel b hb
        hbbase hcart cG m₀ hm₀ hbmodel hBundle
  refine ⟨c₀, a₀, hc₀, ha₀, hco, hn, D, eP, π, hproj, hmap, hπ,
    cD, q, hD, hq, hcartD, hproper, hsmooth, hgc, hopen, hcoverage,
    m, hm, hmq, hlegs, ?_⟩
  intro s j
  refine ⟨?_, ?_, ?_⟩
  · calc
      (projectiveLinePolynomialChart (F.obj s) j ≫
          projectiveAppendChart G i (F.obj s)
            (p s (sel s).val (sel s).property) (c (sel s).val)) ≫ m =
        projectiveLinePolynomialChart (F.obj s) j ≫
          projectiveCoeffMap (ULift.{u} (Fin 2))
            ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
              (eP s).inv ≫ cD.ι.app (.op s) := by rw [Category.assoc, hlegs]
      _ = _ := by
        rw [← Category.assoc,
          projectiveLinePolynomial_coeff (N.obj s) (F.obj s)
            ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) j]
        simp only [Category.assoc]
  · let nleg : Spec (.of (N.obj s)) ⟶ cG.pt.left := (cG.ι.app (.op s)).left
    let πs : D.obj (.op s) ⟶ Spec (.of (N.obj s)) := π.app (.op s)
    have hπs : πs = (eP s).hom ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) :=
      hproj s
    have hqs : cD.ι.app (.op s) ≫ q = πs ≫ nleg := hq (.op s)
    exact polynomial_chart_iso_projection (N.obj s) j (eP s) πs
      (cD.ι.app (.op s)) q nleg hπs hqs
  · let fleg : Spec (.of (F.obj s)) ⟶ bsdhScheme G word := b.app (.op s)
    have hwhole : projectiveToSpec (F.obj s) (ULift.{u} (Fin 2)) ≫ fleg =
        projectiveAppendChart G i (F.obj s)
          (p s (sel s).val (sel s).property) (c (sel s).val) ≫ bsdhAppendFst G word i :=
      (projectiveAppendChart_cartesian G i (F.obj s)
        (p s (sel s).val (sel s).property) (c (sel s).val)
        fleg (bsdhAppendFst G word i) (hcart s)).w
    exact polynomial_chart_projection (F.obj s) j
      (projectiveAppendChart G i (F.obj s)
        (p s (sel s).val (sel s).property) (c (sel s).val))
      (bsdhAppendFst G word i) fleg hwhole

end SchubertGeometry
