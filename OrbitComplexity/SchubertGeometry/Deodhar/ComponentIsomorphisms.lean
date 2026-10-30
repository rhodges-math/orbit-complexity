import OrbitComplexity.SchubertGeometry.Deodhar.ComponentSuccessor
import OrbitComplexity.SchubertGeometry.Deodhar.InitialComponent
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterAll


/-! # Parameter isomorphisms for components

Distinguished subexpressions identify their parameter varieties with the intrinsic components,
compatibly with the flag morphism.
-/
open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
namespace SchubertGeometry.Deodhar
noncomputable section
universe u

private theorem iso_comp_pre {S : Scheme} {A B Y : Over S}
    (e : A ≅ B) (i : B ⟶ Y) [IsPreimmersion i.left] :
    IsPreimmersion (e.hom ≫ i).left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  change IsPreimmersion (e.hom.left ≫ i.left)
  infer_instance

private theorem preiso_range {K : Type u} [Field K] {A B F : Variety K}
    (e : A.toOver ≅ B.toOver) (f : B.toOver ⟶ F.toOver) :
    Set.range (mapPoints (X := A) (Y := F) (e.hom ≫ f)) =
      Set.range (mapPoints (X := B) (Y := F) f) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨mapPoints (X := A) (Y := B) e.hom a,
      (mapPoints_comp (X := A) (Y := B) (Z := F) e.hom f a).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (pointsHomeomorph (X := A) (Y := B) e).surjective b
    exact ⟨a, mapPoints_comp (X := A) (Y := B) (Z := F) e.hom f a⟩

private theorem reverse_flag_comp {C : Type*} [Category C] {A B D E Z : C}
    (a : A ≅ B) (e : A ≅ D) (i : D ⟶ E) (j : E ⟶ Z)
    (pA : A ⟶ Z) (pB : B ⟶ Z)
    (he : e.hom ≫ i ≫ j = pA) (ha : a.hom ≫ pB = pA) :
    (a.symm ≪≫ e).hom ≫ (i ≫ j) = pB := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [he, ← ha, a.inv_hom_id_assoc]

attribute [local irreducible] deodharParameters deodharAllIso

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- Every prefix parameter variety gives its intrinsic component with its flag morphism. -/
private theorem prefixExists
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    ∀ n, n ≤ word.length →
      ∃ e : (deodharParameters G (expression.take n)).toOver ≅
        (deodharPrefixComponent G expression hred n).toOver,
        e.hom ≫ deodharPrefixInclusion G expression hred n ≫
          schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)) =
            deodharPrefixMorphism G (expression.take n) n := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨deodharBaseIso G expression hred, deodharBaseIso_flag G expression hred⟩
  | succ n ih =>
    intro hn
    have hlt : n < word.length := Nat.lt_of_succ_le hn
    obtain ⟨e, he⟩ := ih (Nat.le_of_lt hlt)
    have : IsPreimmersion (deodharPrefixInclusion G expression hred n).left := by
      dsimp only [deodharPrefixInclusion]
      infer_instance
    have := iso_comp_pre (S := Spec (CommRingCat.of K)) e (deodharPrefixInclusion G expression
      hred n)
    have hf : (e.hom ≫ deodharPrefixInclusion G expression hred n) ≫
        schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n)) =
          deodharPrefixMorphism G (expression.take n) n :=
      (Category.assoc _ _ _).trans he
    exact successorNatExists G expression hred hd n hlt
      (e.hom ≫ deodharPrefixInclusion G expression hred n) hf
      (preiso_range (A := deodharParameters G (expression.take n))
        (B := deodharPrefixComponent G expression hred n) (F := wordCell G word n)
        e (deodharPrefixInclusion G expression hred n))

/-- The full parameter variety gives the intrinsic component with its flag morphism. -/
private theorem componentExists
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression) :
    ∃ e : (deodharParameters G expression).toOver ≅
      (deodharComponent G expression hred).toOver,
      e.hom ≫ deodharInclusion G expression hred =
        deodharPrefixMorphism G expression word.length := by
  obtain ⟨e, he⟩ := prefixExists G expression hred hd word.length le_rfl
  exact ⟨(deodharAllIso G expression).symm ≪≫ e,
    reverse_flag_comp (deodharAllIso G expression) e
      (deodharPrefixInclusion G expression hred word.length)
      (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take word.length)))
      (deodharPrefixMorphism G (expression.take word.length) word.length)
      (deodharPrefixMorphism G expression word.length) he (deodharAllIso_flag G expression)⟩

end
end SchubertGeometry.Deodhar

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety
namespace SchubertGeometry
noncomputable section
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

/-- The parameter variety of a distinguished subexpression gives its component. -/
def deodharComponentIso : (deodharParameters G expression).toOver ≅
    (deodharComponent G expression hred).toOver :=
  Classical.choose (Deodhar.componentExists G expression hred hd)

/-- The component chart induces the ordered-product morphism to the flag variety. -/
theorem deodharComponentIso_flag :
    (deodharComponentIso G expression hred hd).hom ≫
      deodharInclusion G expression hred =
        deodharPrefixMorphism G expression word.length :=
  Classical.choose_spec (Deodhar.componentExists G expression hred hd)

end
end SchubertGeometry
