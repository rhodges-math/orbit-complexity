import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Specialization of rational relations

Two dominant maps into an irreducible scheme pull rational functions back to
the function field of their source. A relation between these pullbacks persists
along any morphism for which both composite maps remain dominant. The proof
factors both pullbacks through the stalk at the image of the generic point.

## Main results

* `functionField_relation_specialize`: specialize a polynomial rational relation.
* `functionField_relation_iff`: a dense family detects rational relations.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

variable {X Y Z : Scheme.{u}}
variable [IrreducibleSpace X] [IsIntegral Y] [IrreducibleSpace Z]

private def stalkAtGeneric (f : Y ⟶ X) (y : Y) (hy : f y = genericPoint X) :
    X.functionField →+* Y.presheaf.stalk y :=
  ((X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap y).hom

private lemma stalkAtGeneric_fraction (f : Y ⟶ X) [IsDominant f]
    (y : Y) (hy : f y = genericPoint X) :
    (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (stalkAtGeneric f y hy) =
      functionFieldMap f := by
  change (((X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫ f.stalkMap y) ≫
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)).hom = _
  unfold functionFieldMap
  rw [Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap]
  simp only [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  congr 2
  exact X.presheaf.stalkSpecializes_comp _ _

omit [IsIntegral Y] in
private lemma stalkAtGeneric_comp (f : Y ⟶ X) (s : Z ⟶ Y) [IsDominant (s ≫ f)]
    (hy : f (s (genericPoint Z)) = genericPoint X) :
    (s.stalkMap (genericPoint Z)).hom.comp (stalkAtGeneric f (s (genericPoint Z)) hy) =
      functionFieldMap (s ≫ f) := by
  change (((X.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
    f.stalkMap (s (genericPoint Z))) ≫ s.stalkMap (genericPoint Z)).hom = _
  unfold functionFieldMap
  rw [Scheme.Hom.stalkMap_comp, Category.assoc]
  congr 3

/-- A rational polynomial relation between two dominant pullbacks persists under
a morphism for which both composite maps remain dominant. -/
theorem functionField_relation_specialize (p a : Y ⟶ X) [IsDominant p] [IsDominant a]
    (s : Z ⟶ Y) [IsDominant (s ≫ p)] [IsDominant (s ≫ a)]
    {ι : Type v} (x : ι → X.functionField) (q : MvPolynomial ι X.functionField)
    (hq : MvPolynomial.eval₂Hom (functionFieldMap p)
      (fun i ↦ functionFieldMap a (x i)) q = 0) :
    MvPolynomial.eval₂Hom (functionFieldMap (s ≫ p))
      (fun i ↦ functionFieldMap (s ≫ a) (x i)) q = 0 := by
  let y := s (genericPoint Z)
  have hp : p y = genericPoint X := map_genericPoint (s ≫ p)
  have ha : a y = genericPoint X := map_genericPoint (s ≫ a)
  let rp := stalkAtGeneric p y hp
  let ra := stalkAtGeneric a y ha
  let e := MvPolynomial.eval₂Hom rp (fun i ↦ ra (x i))
  have he : e q = 0 := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_zero, MvPolynomial.map_eval₂Hom]
    simpa only [rp, ra, ← RingHom.comp_apply, stalkAtGeneric_fraction] using hq
  have hs := congrArg (s.stalkMap (genericPoint Z)) he
  rw [map_zero, MvPolynomial.map_eval₂Hom] at hs
  simpa only [rp, ra, y, ← RingHom.comp_apply, stalkAtGeneric_comp] using hs

/-- A family of morphisms whose generic-point images are dense detects polynomial
relations between two dominant rational pullbacks. -/
theorem functionField_relation_iff [IsIntegral Z]
    (p a : Y ⟶ X) [IsDominant p] [IsDominant a]
    {I : Type w} (s : I → (Z ⟶ Y))
    [∀ i, IsDominant (s i ≫ p)] [∀ i, IsDominant (s i ≫ a)]
    (hd : Dense (Set.range (fun i ↦ s i (genericPoint Z))))
    {ι : Type v} (x : ι → X.functionField) (q : MvPolynomial ι X.functionField) :
    MvPolynomial.eval₂Hom (functionFieldMap p)
        (fun i ↦ functionFieldMap a (x i)) q = 0 ↔
      ∀ i, MvPolynomial.eval₂Hom (functionFieldMap (s i ≫ p))
        (fun j ↦ functionFieldMap (s i ≫ a) (x j)) q = 0 := by
  constructor
  · exact fun hq i ↦ functionField_relation_specialize p a (s i) x q hq
  intro hq
  by_contra hn
  let r := MvPolynomial.eval₂Hom (functionFieldMap p)
    (fun i ↦ functionFieldMap a (x i)) q
  have hr : r ≠ 0 := hn
  obtain ⟨U, hU, f, hf⟩ := Y.presheaf.exists_germ_eq r
  have : Nonempty U := ⟨genericPoint Y, hU⟩
  have hbasic : genericPoint Y ∈ Y.basicOpen f := by
    apply (Y.mem_basicOpen f (genericPoint Y) hU).mpr
    rw [hf]
    exact isUnit_iff_ne_zero.mpr hr
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    hd.exists_mem_open (Y.basicOpen f).isOpen ⟨_, hbasic⟩
  let y := s i (genericPoint Z)
  obtain ⟨hyU, hfu⟩ := (Y.mem_basicOpen'' f y).mp hi
  have hp : p y = genericPoint X := map_genericPoint (s i ≫ p)
  have ha : a y = genericPoint X := map_genericPoint (s i ≫ a)
  let rp := stalkAtGeneric p y hp
  let ra := stalkAtGeneric a y ha
  let e := MvPolynomial.eval₂Hom rp (fun j ↦ ra (x j))
  have he : algebraMap (Y.presheaf.stalk y) Y.functionField (e q) = r := by
    rw [MvPolynomial.map_eval₂Hom]
    simp only [rp, ra, ← RingHom.comp_apply, stalkAtGeneric_fraction]
    rfl
  have hf' : algebraMap (Y.presheaf.stalk y) Y.functionField
      (Y.presheaf.germ U y hyU f) = r := by
    rw [Y.algebraMap_germ_eq_germToFunctionField hyU]
    exact hf
  have hfe : Y.presheaf.germ U y hyU f = e q :=
    IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField (hf'.trans he.symm)
  have heu : IsUnit (e q) := hfe ▸ hfu
  have hz : (s i).stalkMap (genericPoint Z) (e q) = 0 := by
    rw [MvPolynomial.map_eval₂Hom]
    simpa only [rp, ra, y, ← RingHom.comp_apply, stalkAtGeneric_comp] using hq i
  exact (heu.map ((s i).stalkMap (genericPoint Z)).hom).ne_zero hz

end

end GroupActions
