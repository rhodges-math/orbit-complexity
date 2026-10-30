import OrbitComplexity.SchubertGeometry.Normality.Transitions.AppendChartCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.CartesianCocone

/-! # The append cocone from the same specified product charts -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem diagram_comp {C : Type v} [Category.{w} C] {X Y A B Z : C}
    (f : X ⟶ Y) (eX : X ⟶ A) (eY : Y ⟶ B) (a : A ⟶ B)
    (p : B ⟶ Z) (q : A ⟶ Z) (hf : f ≫ eY = eX ≫ a) (ha : a ≫ p = q) :
    f ≫ (eY ≫ p) = eX ≫ q := by rw [← Category.assoc, hf, Category.assoc, ha]

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
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
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (e : ∀ s, D.obj (.op s) ≅ projectiveScheme (F.obj s) (ULift.{u} (Fin 2)))
    (hmap : ∀ s t (f : s ⟶ t), D.map f.op ≫ (e s).hom = (e t).hom ≫
      (projectiveLineScalingIso
        (Units.map (simpleBorelCoefficientMap G i (F.obj t)
          (beta t (sel t).val (sel t).property (sel s).val
            ((leOfHom f) (sel s).property))).toRingHom.toMonoidHom
          (simpleRootCoefficient G i))).hom ≫
      (projectiveLineTranslationIso (simpleBorelCoefficientMap G i (F.obj t)
        (beta t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
          simpleRootParameter G))).hom ≫
      projectiveCoeffMap (ULift.{u} (Fin 2)) (F.map f).hom.toRingHom)

/-- The selected charts form a cocone on the all-arrow transition diagram. -/
def appendCocone : Cocone D where
  pt := bsdhScheme G (word ++ [i])
  «ι» :=
    { app := fun s ↦ (e s.unop).hom ≫
        projectiveAppendChart G i (F.obj s.unop)
          (p s.unop (sel s.unop).val (sel s.unop).property) (c (sel s.unop).val)
      naturality := by
        intro s t f
        simp only [Functor.const_obj_map]
        let j := (sel s.unop).val
        let k := (sel t.unop).val
        have hj : j ∈ s.unop.val := (sel s.unop).property
        have hk : k ∈ t.unop.val := (sel t.unop).property
        have hks : k ∈ s.unop.val := (leOfHom f.unop) hk
        have hR : projectiveCoeffMap (ULift.{u} (Fin 2)) (F.map f.unop).hom.toRingHom ≫
            projectiveAppendChart G i (F.obj t.unop) (p t.unop k hk) (c k) =
          projectiveAppendChart G i (F.obj s.unop) (p s.unop k hks) (c k) :=
          (projectiveAppendChart_coeff G i (F.obj t.unop) (F.obj s.unop)
            (F.map f.unop).hom (p t.unop k hk) (c k)).trans
              (congrArg (fun q ↦ projectiveAppendChart G i (F.obj s.unop) q (c k))
                (hpn t.unop s.unop f.unop k hk))
        have hT := projectiveAppendChart_transition G i (F.obj s.unop)
          (p s.unop j hj) (p s.unop k hks) (c j) (c k)
          (beta s.unop j hj k hks) (hchart s.unop j hj k hks)
        have hcomp := (congrArg (fun q ↦
          ((projectiveLineScalingIso
            (Units.map (simpleBorelCoefficientMap G i (F.obj s.unop)
              (beta s.unop j hj k hks)).toRingHom.toMonoidHom (simpleRootCoefficient G i))).hom ≫
            (projectiveLineTranslationIso (simpleBorelCoefficientMap G i (F.obj s.unop)
              (beta s.unop j hj k hks)
              ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) *
                simpleRootParameter G))).hom) ≫ q) hR).trans hT.symm
        exact diagram_comp (D.map f) (e s.unop).hom (e t.unop).hom _ _ _
          (hmap t.unop s.unop f.unop) (by simpa only [Category.assoc] using hcomp) }

/-- The cocone component is exactly the same chart, with its chosen projective presentation. -/
theorem appendCocone_leg (s : {s : Finset J // s.Nonempty}) :
    (@SchubertGeometry.appendCocone.{u} K kField kClosed kZero G word i J V₀
      F p c hpn beta hchart sel D e hmap).ι.app (.op s) =
      (e s).hom ≫ projectiveAppendChart G i (F.obj s)
        (p s (sel s).val (sel s).property) (c (sel s).val) := rfl

end SchubertGeometry
