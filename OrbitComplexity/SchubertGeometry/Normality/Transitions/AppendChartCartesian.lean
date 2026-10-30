import OrbitComplexity.SchubertGeometry.Normality.Transitions.AppendChartCoefficients

/-! # Cartesian squares of the same specified append chart -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem tensor_inv_fst {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    (A : C) {Y P : C} (e : Y ≅ P) :
    (tensorIso (Iso.refl A) e).inv ≫ fst A Y = fst A P := by
  change (𝟙 A ⊗ₘ e.inv) ≫ fst A Y = fst A P
  simpa only [Category.comp_id] using tensorHom_fst (𝟙 A) e.inv

private theorem comp_of_eq {C : Type v} [Category.{w} C] {A B C₀ D : C}
    (f : A ⟶ B) (g : B ⟶ C₀) (h : C₀ ⟶ D) (k : B ⟶ D) (hk : g ≫ h = k) :
    (f ≫ g) ≫ h = f ≫ k := by rw [Category.assoc, hk]

private theorem lineIso_inv_base {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    (simpleBorelLineIso G i A).inv ≫
        (fst ((algSpec (.of K)).obj (.op A))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left =
      projectiveToSpec A (ULift.{u} (Fin 2)) := by
  let SA := (algSpec (.of K)).obj (.op A)
  let Y := (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver
  let T := (Over.forget (Spec (.of K))).mapIso
    (tensorIso (Iso.refl SA) (simpleSchubertIso G i))
  have ht : T.inv ≫ (fst SA Y).left =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (projectiveToSpec K (ULift.{u} (Fin 2))) :=
    congrArg Over.Hom.left (tensor_inv_fst SA (simpleSchubertIso G i))
  exact (comp_of_eq
    (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)).hom T.inv
    (fst SA Y).left _ ht).trans (projectiveBaseChange_fst _ _)

private theorem pullback_source_iso {C : Type v} [Category.{w} C]
    {P X Y Z P' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (e : P' ≅ P) (a : P' ⟶ X) (b : P' ⟶ Y)
    (ha : e.hom ≫ fst = a) (hb : e.hom ≫ snd = b) : IsPullback a b f g :=
  h.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (ha.trans (Category.comp_id a).symm) (hb.trans (Category.comp_id b).symm)
    ((Category.id_comp f).trans (Category.comp_id f).symm)
    ((Category.id_comp g).trans (Category.comp_id g).symm)

/-- The original product-chart pullback square remains cartesian in projective coordinates. -/
theorem projectiveAppendChart_cartesian {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    {V T : Over (Spec (.of K))} {Z : Scheme.{u}}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T)
    (b : Spec (.of A) ⟶ Z) (f : T.left ⟶ Z)
    (hc : IsPullback
      (fst ((algSpec (.of K)).obj (.op A))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p ⊗ₘ 𝟙 _) ≫ c).left b f) :
    IsPullback (projectiveToSpec A (ULift.{u} (Fin 2)))
      (projectiveAppendChart G i A p c) b f := by
  exact pullback_source_iso hc (simpleBorelLineIso G i A).symm _ _
    (lineIso_inv_base G i A) rfl

end SchubertGeometry
