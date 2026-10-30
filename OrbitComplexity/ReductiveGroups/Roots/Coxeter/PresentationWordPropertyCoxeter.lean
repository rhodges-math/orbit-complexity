import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyNormalization

/-!
# The Coxeter system on the Weyl group

Normalize formal words while preserving their formal products, then use
the proved equality of reduced words. This proves injectivity of
the canonical presentation map. Together with simple generation it
constructs the Coxeter system, whose generators and word evaluation are
identified explicitly with the existing simple reflections.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Completeness of the canonical Coxeter presentation on the simple reflections,
proved by formal-product-preserving normalization and reduced-word equality. -/
theorem weylCoxeterPresentationMap_injective (b : P.Base) :
    Function.Injective (weylCoxeterPresentationMap b) := by
  intro x y hxy
  obtain ⟨l, rfl⟩ := (simpleCoxeterMatrix b).toCoxeterSystem.wordProd_surjective x
  obtain ⟨k, rfl⟩ := (simpleCoxeterMatrix b).toCoxeterSystem.wordProd_surjective y
  have hactual : simpleWeylWord b l = simpleWeylWord b k := by simpa only
    [weylCoxeterPresentationMap_wordProd] using hxy
  obtain ⟨u, hu, hulen, huformal⟩ :=
    PresentationWordPropertyNormalization.exists_preserving_reduced_word b l
  obtain ⟨v, hv, hvlen, hvformal⟩ :=
    PresentationWordPropertyNormalization.exists_preserving_reduced_word b k
  have hured : rootInversionCount b (simpleWeylWord b u) = u.length := by rw [hu, hulen]
  have hvred : rootInversionCount b (simpleWeylWord b v) = v.length := by rw [hv, hvlen]
  have hformal := presentationWordProd_eq_of_reduced b u v hured hvred
    (hu.trans (hactual.trans hv.symm))
  exact huformal.symm.trans (hformal.trans hvformal)

/-- The proved presentation isomorphism, in the same direction as the
original canonical homomorphism. -/
def weylCoxeterPresentationEquiv (b : P.Base) :
    (simpleCoxeterMatrix b).Group ≃* P.weylGroup :=
  MulEquiv.ofBijective (weylCoxeterPresentationMap b)
    ⟨weylCoxeterPresentationMap_injective b, weylCoxeterPresentationMap_surjective b⟩

/-- The equality is

```lean
weylCoxeterPresentationEquiv b w = weylCoxeterPresentationMap b w
```
-/
@[simp] theorem weylCoxeterPresentationEquiv_apply (b : P.Base)
    (w : (simpleCoxeterMatrix b).Group) :
    weylCoxeterPresentationEquiv b w = weylCoxeterPresentationMap b w := rfl

/-- The Weyl Coxeter system is constructed from the proved
presentation isomorphism; it is not an additional hypothesis. -/
def weylCoxeterSystem (b : P.Base) : CoxeterSystem (simpleCoxeterMatrix b) P.weylGroup :=
  (simpleCoxeterMatrix b).toCoxeterSystem.map (weylCoxeterPresentationEquiv b)

/-- Its simple generators are precisely the existing root reflections. -/
@[simp] theorem weylCoxeterSystem_simple (b : P.Base) (i : b.support) :
    (weylCoxeterSystem b).simple i = RootPairing.weylGroup.ofIdx P i := by
  change weylCoxeterPresentationMap b ((simpleCoxeterMatrix b).simple i) = _
  exact weylCoxeterPresentationMap_simple b i

/-- Its word convention agrees exactly with the existing word convention. -/
@[simp] theorem weylCoxeterSystem_wordProd (b : P.Base) (l : List b.support) :
    (weylCoxeterSystem b).wordProd l = simpleWeylWord b l := by
  induction l with
  | nil => simp [simpleWeylWord]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, weylCoxeterSystem_simple, ih]
    rfl

end ReductiveGroups
