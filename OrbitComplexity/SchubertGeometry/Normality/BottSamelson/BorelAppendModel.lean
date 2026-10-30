import OrbitComplexity.SchubertGeometry.Normality.Bundles.BorelModelBundle
import OrbitComplexity.SchubertGeometry.Normality.Bundles.BundleComparison
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveDiagramComparison

/-! # comparison of the same retained arithmetic Borel bundle -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open FrobeniusSplitting CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem cancel_chart {C : Type v} [Category.{w} C] {X P Y Q Z : C}
    (e : X ≅ P) (a : P ⟶ Y) (b : P ⟶ Q) (m : Y ⟶ Z) (c : Q ⟶ Z)
    (h : (e.hom ≫ a) ≫ m = (e.hom ≫ b) ≫ c) : a ≫ m = b ≫ c := by
  apply (cancel_epi e.hom).1
  simpa only [Category.assoc] using h

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

/-- The retained Borel bundle has the append as its scalar fibre. -/
theorem borel_append_comparison :
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
            ∀ s, projectiveAppendChart G i (F.obj s)
                (p s (sel s).val (sel s).property) (c (sel s).val) ≫ m =
              projectiveCoeffMap (ULift.{u} (Fin 2))
                ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
                  (eP s).inv ≫ cD.ι.app (.op s) := by
  classical
  dsimp only
  intro H
  obtain ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀, DN, eN, πN, hprojN, hmapN, hπN,
    cD, q, ⟨hD⟩, hq, hcartD, hproper, hsmooth, hgc, hopen, hcover⟩ := H
  let scale := fun s j hj k hk ↦
    Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  have hco s j hj k hk l hl : scale s j hj l hl = scale s k hk l hl * scale s j hj k hk ∧
      shift s j hj l hl = (scale s k hk l hl : F.obj s) * shift s j hj k hk + shift s k hk l hl :=
    (simpleBorelCoefficient_laws G i (F.obj s)).2.2.2
      (beta s j hj k hk) (beta s k hk l hl) (beta s j hj l hl) (hbeta s j hj k hk l hl)
  have hn s t (f : s ⟶ t) j hj k hk :
      Units.map (F.map f).hom.toRingHom.toMonoidHom (scale s j hj k hk) =
        scale t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (shift s j hj k hk) = shift t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
    have hh := (simpleBorelCoefficient_natural G i (F.obj s) (F.obj t)
      (F.map f).hom (beta s j hj k hk)).2
    rw [CommAlgCat.ofHom_hom, ← hnatural] at hh
    exact ⟨hh.1.symm, hh.2.symm⟩
  obtain ⟨DF, eF, πF, hprojF, hmapF, hπF⟩ := exists_projective_transition F sel scale shift hco hn
  let v := modelEvaluation N F e he
  have hc s j hj k hk : Units.map (v.app s).hom.toMonoidHom (c₀ s j hj k hk) =
      scale s j hj k hk := by
    apply Units.ext
    exact hc₀ s j hj k hk
  have ha s j hj k hk : (v.app s).hom (a₀ s j hj k hk) = shift s j hj k hk := ha₀ s j hj k hk
  let τ := projectiveDiagramComparison N F v DN DF eN eF
    (fun s t f ↦ c₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
    (fun s t f ↦ a₀ t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
    hmapN (fun s t f ↦ by simpa only [hc, ha] using hmapF s t f)
  let cX := @SchubertGeometry.appendCocone.{u} K kField kClosed kZero
    G word i J V₀ F p c hpn beta hchart sel DF eF hmapF
  let {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t) :
      IsOpenImmersion ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))).map f) :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let dOpen : ∀ {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t),
      IsOpenImmersion (DN.map f) := fun f =>
    MorphismProperty.of_isPullback (hπN f).flip inferInstance
  let dDir : (DN ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective πN hπN (fun f ↦ (DN.map f).injective)
  obtain ⟨m, hm, hmq, hlegs⟩ := @SchubertGeometry.exists_bundle_comparison.{u} K R kField kClosed
    kZero rComm rKAlg
    G word i J V₀ F N e fOpen fDir p c sel DF DN dOpen dDir eF eN πF hπF hprojF πN hprojN cX.ι (fun
      s ↦ rfl) b hb hbbase hcart cG cD hD q
    (fun s ↦ hq (.op s)) m₀ hm₀ hbmodel τ (fun s ↦ rfl)
  refine ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀, DN, eN, πN, hprojN, hmapN, hπN,
    cD, q, ⟨hD⟩, hq, hcartD, hproper, hsmooth, hgc, hopen, hcover, m, hm, hmq, ?_⟩
  intro s
  exact (cancel_chart (eF s) _ _ _ _ (hlegs s)).trans (Category.assoc _ _ _)

end SchubertGeometry
