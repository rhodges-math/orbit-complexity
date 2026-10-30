import OrbitComplexity.BruhatIntervals.Words.Prefix
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixLifts

/-! # Taking all parameters

The full-length prefix agrees with its subexpression. Transport through this equality
identifies their parameter varieties and preserves the regular flag morphism.
-/

open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions GroupActions.Variety SchubertGeometry
namespace SchubertGeometry
noncomputable section
universe u

private theorem subexpression_ext {S : Type*} {word : List S}
    (a b : Subexpression word) (h : a.choices = b.choices) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem cast_choices {S : Type*} {word word' : List S} (h : word = word')
    (e : Subexpression word) : (h ▸ e).choices = e.choices := by
  subst word'
  rfl

private theorem sigma_eq_cast {I : Type*} {F : I → Type*} {a b : I}
    (h : a = b) (e : F a) (e' : F b) (he : h ▸ e = e') :
    (⟨a, e⟩ : Sigma F) = ⟨b, e'⟩ := by
  subst b
  subst e'
  rfl

private theorem takeAllPair {S : Type*} {word : List S} (e : Subexpression word) :
    (⟨word.take word.length, e.take word.length⟩ : Σ w : List S, Subexpression w) =
      ⟨word, e⟩ := by
  have hw : word.take word.length = word := List.take_length
  apply sigma_eq_cast hw
  apply subexpression_ext
  exact (cast_choices hw (e.take word.length)).trans (by
    change e.choices.take word.length = e.choices
    rw [← e.length_choices, List.take_length])

private theorem familyMap_cast {C I : Type*} [Category C] (F : I → C) {Z : C}
    (f : ∀ i, F i ⟶ Z) {a b : I} (h : a = b) :
    (eqToIso (congrArg F h)).hom ≫ f b = f a := by
  subst b
  simp

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

attribute [local irreducible] deodharParameters

/-- Taking all letters preserves the parameter variety. -/
def deodharAllIso :
    (deodharParameters G (expression.take word.length)).toOver ≅
      (deodharParameters G expression).toOver :=
  eqToIso (congrArg
    (fun i : Σ w : List G.rootBase.support, Subexpression w =>
      (deodharParameters G i.2).toOver) (takeAllPair expression))

/-- The all-letter parameter comparison preserves the full prefix flag morphism. -/
theorem deodharAllIso_flag :
    (deodharAllIso G expression).hom ≫ deodharPrefixMorphism G expression word.length =
      deodharPrefixMorphism G (expression.take word.length) word.length :=
  familyMap_cast
    (fun i : Σ w : List G.rootBase.support, Subexpression w =>
      (deodharParameters G i.2).toOver)
    (fun i => deodharPrefixMorphism G i.2 word.length) (takeAllPair expression)

end
end SchubertGeometry
