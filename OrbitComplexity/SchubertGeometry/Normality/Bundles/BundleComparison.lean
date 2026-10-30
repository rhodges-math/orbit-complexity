import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.AppendColimit
import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveComparisonSquares
import OrbitComplexity.FrobeniusSplitting.Normality.Models.SpecifiedCartesianComparison

/-! # Comparison with the append over the same covered arithmetic base -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem coefficient_base {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec A (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← projectiveBaseChange_snd (ULift.{u} (Fin 2)) f, Category.assoc,
    ← pullback.condition, ← Category.assoc, projectiveBaseChange_fst]

private theorem chart_square {C : Type v} [Category.{w} C]
    {L P A Z T : C} (e : L ⟶ P) (proj : P ⟶ A) (chart : P ⟶ Z)
    (b : A ⟶ T) (f : Z ⟶ T) (π : L ⟶ A) (leg : L ⟶ Z)
    (hπ : π = e ≫ proj) (hleg : leg = e ≫ chart) (hw : proj ≫ b = chart ≫ f) :
    leg ≫ f = π ≫ b := by rw [hleg, hπ, Category.assoc, ← hw, ← Category.assoc]

private theorem scalar_base {C : Type v} [Category.{w} C]
    {L P A Z T S : C} (leg : L ⟶ Z) (f : Z ⟶ T) (z : Z ⟶ S) (t : T ⟶ S)
    (π : L ⟶ A) (b : A ⟶ T) (c : A ⟶ S) (e : L ⟶ P) (p : P ⟶ A)
    (hz : f ≫ t = z) (hleg : leg ≫ f = π ≫ b) (hb : b ≫ t = c)
    (hπ : π = e ≫ p) : leg ≫ z = e ≫ p ≫ c := by
  rw [← hz, ← Category.assoc, hleg, Category.assoc, hb, hπ, Category.assoc]

private theorem model_base {C : Type v} [Category.{w} C]
    {L P A T B S : C} (leg : L ⟶ T) (q : T ⟶ B) (c : B ⟶ S)
    (π : L ⟶ A) (b : A ⟶ B) (s : A ⟶ S) (e : L ⟶ P) (p : P ⟶ A)
    (hleg : leg ≫ q = π ≫ b) (hb : b ≫ c = s) (hπ : π = e ≫ p) :
    leg ≫ (q ≫ c) = e ≫ p ≫ s := by
  rw [← Category.assoc, hleg, Category.assoc, hb, hπ, Category.assoc]

private theorem comparison_base {C : Type v} [Category.{w} C]
    {L M P Q A B : C} (eX : L ≅ P) (eY : M ≅ Q) (f : P ⟶ Q)
    (p : P ⟶ A) (q : Q ⟶ B) (b : A ⟶ B) (τ : L ⟶ M)
    (πL : L ⟶ A) (πM : M ⟶ B) (hτ : τ = eX.hom ≫ f ≫ eY.inv)
    (hπL : πL = eX.hom ≫ p) (hπM : πM = eY.hom ≫ q)
    (hb : f ≫ q = p ≫ b) : τ ≫ πM = πL ≫ b := by
  rw [hτ, hπM, hπL]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hb]

private theorem bundle_square {C : Type v} [Category.{w} C]
    {P Q X Y A B X₀ C₀ : C}
    (legX : P ⟶ X) (τ : P ⟶ Q) (legY : Q ⟶ Y) (q : Y ⟶ B)
    (πX : P ⟶ A) (πY : Q ⟶ C₀) (a : A ⟶ C₀)
    (legA : A ⟶ X₀) (legC : C₀ ⟶ B) (f : X ⟶ X₀) (m : X ⟶ Y) (m₀ : X₀ ⟶ B)
    (hlegs : legX ≫ m = τ ≫ legY) (hmodel : legY ≫ q = πY ≫ legC)
    (hτ : τ ≫ πY = πX ≫ a) (hbase : legA ≫ m₀ = a ≫ legC)
    (hnative : legX ≫ f = πX ≫ legA) :
    legX ≫ (m ≫ q) = legX ≫ (f ≫ m₀) := by
  rw [← Category.assoc, hlegs, Category.assoc, hmodel, ← Category.assoc, hτ,
    Category.assoc, ← hbase, ← Category.assoc, ← hnative, Category.assoc]

/-- The same projective diagram compares the append to the specified arithmetic bundle. -/
theorem exists_bundle_comparison {K R : Type u} [kField : Field K] [kClosed : IsAlgClosed K]
    [kZero : CharZero K] [rComm : CommRing R] [rKAlg : Algebra R K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (DF DN : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    [dOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (DN.map f)]
    [dDir : (DN ⋙ Scheme.forget).IsLocallyDirected]
    (eF : ∀ s, DF.obj (.op s) ≅ projectiveScheme (F.obj s) (ULift.{u} (Fin 2)))
    (eN : ∀ s, DN.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (πF : DF ⟶ F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K)))
    (hπF : πF.Equifibered)
    (hprojF : ∀ s, πF.app (.op s) = (eF s).hom ≫ projectiveToSpec (F.obj s)
      (ULift.{u} (Fin 2)))
    (πN : DN ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (hprojN : ∀ s, πN.app (.op s) = (eN s).hom ≫ projectiveToSpec (N.obj s)
      (ULift.{u} (Fin 2)))
    (legs : DF ⟶ (Functor.const _).obj (bsdhScheme G (word ++ [i])))
    (hleg : ∀ s, legs.app (.op s) = (eF s).hom ≫
      projectiveAppendChart G i (F.obj s) (p s (sel s).val (sel s).property)
        (c (sel s).val))
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
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (cD : Cocone DN) (hD : IsColimit cD)
    (q : cD.pt ⟶ cG.pt.left)
    (hq : ∀ s, cD.ι.app (.op s) ≫ q = πN.app (.op s) ≫ (cG.ι.app (.op s)).left)
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hbmodel : ∀ s, b.app (.op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left)
    (τ : DF ⟶ DN)
    (hτ : ∀ s, τ.app (.op s) = (eF s).hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2))
      ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫ (eN s).inv) :
    ∃ m : bsdhScheme G (word ++ [i]) ⟶ cD.pt,
      IsPullback m (bsdhToSpec G (word ++ [i])) (q ≫ cG.pt.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsPullback m (bsdhAppendFst G word i) q m₀ ∧
      ∀ s, legs.app (.op s) ≫ m = τ.app (.op s) ≫ cD.ι.app (.op s) := by
  let cX := Cocone.mk (bsdhScheme G (word ++ [i])) legs
  let hX := @SchubertGeometry.appendCoconeIsColimit.{u} K kField kClosed kZero
    G word i J V₀ F fOpen fDir p c sel DF eF πF hπF hprojF legs hleg b hb hcart
  have hnative (s) : legs.app (.op s) ≫ bsdhAppendFst G word i =
      πF.app (.op s) ≫ b.app (.op s) := by
    have H := projectiveAppendChart_cartesian G i (F.obj s)
      (p s (sel s).val (sel s).property) (c (sel s).val)
      (b.app (.op s)) (bsdhAppendFst G word i) (hcart s)
    exact chart_square (eF s).hom _ _ _ _ _ _ (hprojF s) (hleg s) H.w
  have hnativebase (s) : legs.app (.op s) ≫ bsdhToSpec G (word ++ [i]) =
      (eF s).hom ≫ projectiveToSpec (F.obj s) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))) := by
    exact SchubertGeometry.scalar_base _ _ _ _ _ _ _ _ _ (bsdhAppendFst_toSpec G word i)
      (hnative s) (hbbase s) (hprojF s)
  have hmodelbase (s) : cD.ι.app (.op s) ≫ (q ≫ cG.pt.hom) =
      (eN s).hom ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := by
    have hw : (cG.ι.app (.op s)).left ≫ cG.pt.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := (cG.ι.app (.op s)).w
    exact model_base _ _ _ _ _ _ _ _ (hq s) hw (hprojN s)
  have hτbase (s) : τ.app (.op s) ≫ πN.app (.op s) = πF.app (.op s) ≫
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) := by
    exact comparison_base (eF s) (eN s) _ _ _ _ _ _ _ (hτ s) (hprojF s) (hprojN s)
      (coefficient_base _)
  obtain ⟨m, hm, hlegs⟩ := FrobeniusSplitting.exists_specified_comparison DF DN τ cX cD hX hD
    (bsdhToSpec G (word ++ [i])) (q ≫ cG.pt.hom)
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (fun s ↦ by
      change IsPullback (τ.app s) (legs.app s ≫ bsdhToSpec G (word ++ [i]))
        (cD.ι.app s ≫ (q ≫ cG.pt.hom)) _
      rw [hnativebase, hmodelbase, hτ]
      exact projectiveComparison_cartesian (e s.unop) (eF s.unop) (eN s.unop))
  have hcomm : m ≫ q = bsdhAppendFst G word i ≫ m₀ := by
    apply hX.hom_ext
    intro s
    change legs.app s ≫ (m ≫ q) = legs.app s ≫ (bsdhAppendFst G word i ≫ m₀)
    exact bundle_square _ _ _ _ _ _ _ _ _ _ _ _ (hlegs s) (hq s.unop)
      (hτbase s.unop) (hbmodel s.unop) (hnative s.unop)
  have hm' : IsPullback m (bsdhAppendFst G word i ≫ bsdhToSpec G word)
      (q ≫ cG.pt.hom) (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    simpa only [bsdhAppendFst_toSpec] using hm
  exact ⟨m, hm, hm'.of_bot hcomm hm₀, fun s ↦ hlegs (.op s)⟩

end SchubertGeometry
