import OrbitComplexity.SchubertGeometry.Normality.Transitions.AppendCocone

/-! # Identification of the append with the specified chart colimit -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u v w
namespace SchubertGeometry

private theorem pullback_source_iso {C : Type v} [Category.{w} C]
    {P X Y Z P' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (e : P' ≅ P) (a : P' ⟶ X) (b : P' ⟶ Y)
    (ha : e.hom ≫ fst = a) (hb : e.hom ≫ snd = b) : IsPullback a b f g :=
  h.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (ha.trans (Category.comp_id a).symm) (hb.trans (Category.comp_id b).symm)
    ((Category.id_comp f).trans (Category.comp_id f).symm)
    ((Category.id_comp g).trans (Category.comp_id g).symm)

/-- The append is the colimit of its same selected projective chart diagram. -/
def appendCoconeIsColimit {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K]
    [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (D : {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (e : ∀ s, D.obj (.op s) ≅ projectiveScheme (F.obj s) (ULift.{u} (Fin 2)))
    (π : D ⟶ F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K)))
    (hπ : π.Equifibered)
    (hproj : ∀ s, π.app (.op s) = (e s).hom ≫
      projectiveToSpec (F.obj s) (ULift.{u} (Fin 2)))
    (legs : D ⟶ (Functor.const _).obj (bsdhScheme G (word ++ [i])))
    (hleg : ∀ s, legs.app (.op s) = (e s).hom ≫ projectiveAppendChart G i (F.obj s)
      (p s (sel s).val (sel s).property) (c (sel s).val))
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (hb : IsColimit (Cocone.mk (bsdhScheme G word) b))
    (hcart : ∀ s, IsPullback
      (fst ((algSpec (.of K)).obj (.op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (.op s)) (bsdhAppendFst G word i)) :
    IsColimit (Cocone.mk (bsdhScheme G (word ++ [i])) legs) := by
  let {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t) :
      IsOpenImmersion ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))).map f) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (F.map f.unop).hom.toRingHom))
    infer_instance
  apply FrobeniusSplitting.cartesianCoconeIsColimit D
    (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) π hπ
    (Cocone.mk _ legs) (Cocone.mk _ b) hb (bsdhAppendFst G word i)
  intro s
  have hP := projectiveAppendChart_cartesian G i (F.obj s.unop)
    (p s.unop (sel s.unop).val (sel s.unop).property) (c (sel s.unop).val)
    (b.app s) (bsdhAppendFst G word i) (hcart s.unop)
  exact pullback_source_iso hP (e s.unop) _ _
    (hproj s.unop).symm (hleg s.unop).symm

end SchubertGeometry
