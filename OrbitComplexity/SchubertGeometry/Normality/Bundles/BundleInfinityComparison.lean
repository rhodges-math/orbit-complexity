import OrbitComplexity.SchubertGeometry.Normality.Bundles.BundleInfinity
import OrbitComplexity.SchubertGeometry.Normality.Models.BsdhInfinity
import Batteries.Tactic.Lint

/-! # The same arithmetic infinity section and the omitted step -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReductiveGroups GroupActions CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem infinity_coefficient {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    projectiveLineSection S (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      Spec.map (CommRingCat.ofHom f) ≫ projectiveLineSection R ⟨1⟩ := by
  rw [projectiveLineSection, Category.assoc, projectiveLinePolynomial_coeff,
    ← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (Polynomial.mapRingHom f) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)) =
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) ≫ CommRingCat.ofHom f from by
    apply CommRingCat.hom_ext
    change (Polynomial.evalRingHom (0 : S)).comp (Polynomial.mapRingHom f) =
      f.comp (Polynomial.evalRingHom (0 : R))
    ext x <;> simp]
  simp only [Spec.map_comp, Category.assoc, projectiveLineSection]

private theorem compare_section_legs {C : Type v} [Category.{w} C]
    {A B P Q X Y Z W : C}
    (s : A ⟶ P) (t : B ⟶ Q) (v : A ⟶ B) (w : P ⟶ Q)
    (k : P ⟶ X) (h : Q ⟶ Y) (b : A ⟶ Z) (l : B ⟶ W)
    (d : Z ⟶ X) (m : X ⟶ Y) (n : Z ⟶ W) (δ : W ⟶ Y)
    (hs : s ≫ k = b ≫ d) (hv : s ≫ w = v ≫ t)
    (hk : k ≫ m = w ≫ h) (hl : l ≫ δ = t ≫ h)
    (hb : b ≫ n = v ≫ l) :
    b ≫ (d ≫ m) = b ≫ (n ≫ δ) := by
  calc
    _ = (s ≫ k) ≫ m := by rw [hs, Category.assoc]
    _ = (s ≫ w) ≫ h := by rw [Category.assoc, hk, Category.assoc]
    _ = v ≫ (t ≫ h) := by rw [hv, Category.assoc]
    _ = (v ≫ l) ≫ δ := by rw [← hl, Category.assoc]
    _ = b ≫ (n ≫ δ) := by rw [← hb, Category.assoc]

private theorem selected_projection {B : Scheme.{u}} {V U Y Z T : Over B}
    (p : V ⟶ U) (b : U ⟶ Z) (c : V ⊗ Y ⟶ T)
    (π : T.left ⟶ Z.left) (v : V.left ⟶ Z.left)
    (h : c.left ≫ π = (fst V Y).left ≫ v)
    (hp : p.left ≫ b.left = v) :
    c.left ≫ π = (fst V Y).left ≫ (p ≫ b).left := by
  exact h.trans (congrArg (fun f => (fst V Y).left ≫ f) hp.symm)

private theorem tensor_endpoint {B : Scheme.{u}} {V U A Y T : Over B}
    {Z W : Scheme.{u}} (p : V ⟶ U) (a : U ⟶ A) (c : U ⊗ Y ⟶ T)
    (f : T.left ⟶ Z) (g : Z ⟶ W) (h : (A ⊗ Y).left ⟶ W)
    (hc : c.left ≫ f ≫ g = (a ⊗ₘ 𝟙 Y).left ≫ h) :
    (((p ⊗ₘ 𝟙 Y) ≫ c).left) ≫ f ≫ g = ((p ≫ a) ⊗ₘ 𝟙 Y).left ≫ h := by
  change (p ⊗ₘ 𝟙 Y).left ≫ c.left ≫ f ≫ g = _
  rw [hc]
  rw [← Category.assoc, ← Over.comp_left, tensorHom_comp_tensorHom, Category.comp_id]

private theorem endpoint_precompose {B : Scheme.{u}} {V U A T : Over B}
    {Z : Scheme.{u}} (p : V ⟶ U) (a : U ⟶ A) (b : U ⟶ T)
    (f : A.left ⟶ Z) (g : T.left ⟶ Z) (h : a.left ≫ f = b.left ≫ g) :
    (p ≫ a).left ≫ f = (p ≫ b).left ≫ g := by
  simpa only [Over.comp_left, Category.assoc] using
    congrArg (fun z => p.left ≫ z) h

private theorem projective_precompose {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (G : ReductiveGroupData K) (i : G.rootBase.support)
    (A : CommAlgCat.{u} K) {V T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T) :
    projectiveAppendChart G i A (𝟙 _) ((p ⊗ₘ 𝟙 _) ≫ c) =
      projectiveAppendChart G i A p c := by
  simp only [projectiveAppendChart, id_tensorHom_id, Category.id_comp]

private theorem identity_base_leg {B : Scheme.{u}} {V U Z : Over B} {X : Scheme.{u}}
    (p : V ⟶ U) (b : U ⟶ Z) (d : Z.left ⟶ X) :
    (𝟙 V : V ⟶ V).left ≫ (p ≫ b).left ≫ d = (p.left ≫ b.left) ≫ d := by
  simp only [Over.id_left, Over.comp_left, Category.id_comp, Category.assoc]

/-- The infinity section on the specified arithmetic chart colimit is the
omitted-step section under the same append comparison. -/
theorem bundle_infinity_comparison {K R : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    [rComm : CommRing R] [rKAlg : Algebra R K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (b₀ : ∀ j, V₀ j ⟶ Over.mk (bsdhToSpec G word))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ V₀ j)
    (g : J → G.points)
    (a : ∀ j, V₀ j ⟶
      (oppositeUnipotentVariety G).toOver)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (ha : ∀ j, (a j).left ≫ flagSchemeChart G (g j) = (b₀ j).left ≫ bsdhMap G word)
    (hend : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g j))
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (hb : IsColimit (Cocone.mk (bsdhScheme G word) b))
    (hp : ∀ s j hj, (p s j hj).left ≫ (b₀ j).left = b.app (.op s))
    (hc : ∀ s,
      (((p s (sel s).val (sel s).property ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c (sel s).val).left) ≫
          bsdhAppendFst G word i =
        (fst ((algSpec (.of K)).obj (.op (F.obj s)))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
            b.app (.op s))
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (.op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (δ : cG.pt.left ⟶ cD.pt)
    (hδ : ∀ s, (cG.ι.app (.op s)).left ≫ δ =
      projectiveLineSection (N.obj s) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
        (eP s).inv ≫ cD.ι.app (.op s))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (m : bsdhScheme G (word ++ [i]) ⟶ cD.pt)
    (hbmodel : ∀ s, b.app (.op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left)
    (hchart : ∀ s, projectiveAppendChart G i (F.obj s)
      (p s (sel s).val (sel s).property) (c (sel s).val) ≫ m =
      projectiveCoeffMap (ULift.{u} (Fin 2))
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) ≫
          (eP s).inv ≫ cD.ι.app (.op s))
    (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G word i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word) :
    d ≫ m = m₀ ≫ δ := by
  apply hb.hom_ext
  intro s
  let j := sel s.unop
  have hπ := selected_projection
    (p s.unop j.val j.property) (b₀ j.val)
    ((p s.unop j.val j.property ⊗ₘ 𝟙 _) ≫ c j.val)
    (bsdhAppendFst G word i) (b.app s) (hc s.unop) (hp s.unop j.val j.property)
  have hEnd := tensor_endpoint (p s.unop j.val j.property) (a j.val) (c j.val)
    (bsdhAppendIso G word i).hom.left
    (pullback.snd (bsdhMap G word) (flagBundleProjection G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))))
    (flagBundleChart G _ (g j.val)) (hend j.val)
  have hA := endpoint_precompose (p s.unop j.val j.property) (a j.val) (b₀ j.val)
    (flagSchemeChart G (g j.val)) (bsdhMap G word) (ha j.val)
  have Hinfty := @bsdh_omitted_infinity.{u} K kField kClosed kZero G
    word i d hdπ hdτ ((algSpec (.of K)).obj (.op (F.obj s.unop)))
    (p s.unop j.val j.property ≫ b₀ j.val) (F.obj s.unop) (𝟙 _)
    (g j.val) (p s.unop j.val j.property ≫ a j.val)
    ((p s.unop j.val j.property ⊗ₘ 𝟙 _) ≫ c j.val) hπ hEnd hA
  have Hnative : projectiveLineSection (F.obj s.unop) (⟨1⟩ : ULift.{u} (Fin 2)) ≫
      projectiveAppendChart G i (F.obj s.unop)
        (p s.unop j.val j.property) (c j.val) = b.app s ≫ d := by
    have hRefine := congrArg
      (fun f => projectiveLineSection (F.obj s.unop) (⟨1⟩ : ULift.{u} (Fin 2)) ≫ f)
      (projective_precompose G i (F.obj s.unop)
        (p s.unop j.val j.property) (c j.val)).symm
    have hBase := (identity_base_leg (p s.unop j.val j.property) (b₀ j.val) d).trans
      (congrArg (fun z => z ≫ d) (hp s.unop j.val j.property))
    exact hRefine.trans (Hinfty.trans hBase)
  exact compare_section_legs
    (projectiveLineSection (F.obj s.unop) (⟨1⟩ : ULift.{u} (Fin 2)))
    (projectiveLineSection (N.obj s.unop) (⟨1⟩ : ULift.{u} (Fin 2)))
    (Spec.map (CommRingCat.ofHom
      ((e s.unop).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
    (projectiveCoeffMap (ULift.{u} (Fin 2))
      ((e s.unop).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
    (projectiveAppendChart G i (F.obj s.unop)
      (p s.unop j.val j.property) (c j.val))
    ((eP s.unop).inv ≫ cD.ι.app s) (b.app s) (cG.ι.app s).left
    d m m₀ δ Hnative (infinity_coefficient _)
    (hchart s.unop) (hδ s.unop) (hbmodel s.unop)

end SchubertGeometry
