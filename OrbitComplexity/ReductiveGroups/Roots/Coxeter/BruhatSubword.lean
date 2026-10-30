import OrbitComplexity.ReductiveGroups.Roots.Coxeter.SubwordBraid
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSubgroup
import OrbitComplexity.ReductiveGroups.Roots.Inversions.InversionProduct

/-!
# Ordinary strong Bruhat order from reduced subwords

The relation has its standard subword definition: a reduced word
for the smaller element is a sublist of a reduced word for
the larger element. Braid transport proves independence of the
chosen larger reduced expression.
-/

noncomputable section

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]

/-- Ordinary strong Bruhat order on the Weyl group, expressed by
subwords of reduced expressions in the simple reflections. -/
def WeylBruhatLE (b : P.Base) (u v : P.weylGroup) : Prop :=
  ∃ l k : List b.support, k.Sublist l ∧
    simpleWeylWord b l = v ∧ simpleWeylWord b k = u ∧
    rootInversionCount b (simpleWeylWord b l) = l.length ∧
    rootInversionCount b (simpleWeylWord b k) = k.length

/-- The ordinary subword criterion holds in any specified reduced
expression, not just in the expression by the definition. -/
theorem weylBruhatLE_iff_subword (b : P.Base) (u : P.weylGroup) (l : List b.support)
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length) :
    WeylBruhatLE b u (simpleWeylWord b l) ↔
      ∃ k : List b.support, k.Sublist l ∧ simpleWeylWord b k = u ∧
        rootInversionCount b (simpleWeylWord b k) = k.length := by
  constructor
  · rintro ⟨l', k', hk', hprod, hkprod, hl', _⟩
    obtain ⟨k, hk, hkeq, hkred⟩ := reduced_subword_transport_of_word_eq b l' l hl' hl hprod hk'
    exact ⟨k, hk, hkeq.trans hkprod, hkred⟩
  · rintro ⟨k, hk, hprod, hkred⟩
    exact ⟨l, k, hk, rfl, hprod, hl, hkred⟩

/-- Any subword product lies below the product of the reduced ambient
word; the subword itself can be reduced by deletion within its positions. -/
theorem weylBruhatLE_of_sublist (b : P.Base) {l k : List b.support}
    (hl : rootInversionCount b (simpleWeylWord b l) = l.length) (hk : k.Sublist l) :
    WeylBruhatLE b (simpleWeylWord b k) (simpleWeylWord b l) := by
  obtain ⟨r, hr, hprod, hlen⟩ := simpleWeylWord_has_reduced_sublist b k
  exact (weylBruhatLE_iff_subword b _ l hl).mpr
    ⟨r, hr.trans hk, hprod, by rw [hprod, hlen]⟩

/-- For these parameters,

```lean
WeylBruhatLE b w w
```
-/
theorem WeylBruhatLE.refl (b : P.Base) (w : P.weylGroup) : WeylBruhatLE b w w := by
  obtain ⟨l, hprod, hlen⟩ := InversionLength.exists_of_inversionCount_length b w
  exact ⟨l, l, .refl _, hprod, hprod, by rw [hprod, hlen], by rw [hprod, hlen]⟩

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The inclusion is

```lean
rootInversionCount b u ≤ rootInversionCount b v
```
-/
theorem WeylBruhatLE.length_le {b : P.Base} {u v : P.weylGroup}
    (h : WeylBruhatLE b u v) : rootInversionCount b u ≤ rootInversionCount b v := by
  obtain ⟨l, k, hk, rfl, rfl, hlred, hkred⟩ := h
  rw [hlred, hkred]
  exact hk.length_le

/-- For these parameters,

```lean
WeylBruhatLE b u w
```
-/
theorem WeylBruhatLE.trans {b : P.Base} {u v w : P.weylGroup}
    (huv : WeylBruhatLE b u v) (hvw : WeylBruhatLE b v w) : WeylBruhatLE b u w := by
  obtain ⟨l, k, hk, hprod, hkprod, hlred, hkred⟩ := hvw
  rw [← hkprod] at huv
  obtain ⟨p, hp, hpprod, hpred⟩ := (weylBruhatLE_iff_subword b u k hkred).mp huv
  exact ⟨l, p, hp.trans hk, hprod, hpprod, hlred, hpred⟩

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The equality is

```lean
u = v
```
-/
theorem WeylBruhatLE.eq_of_length_eq {b : P.Base} {u v : P.weylGroup}
    (h : WeylBruhatLE b u v) (hlen : rootInversionCount b u = rootInversionCount b v) :
    u = v := by
  obtain ⟨l, k, hk, hprod, hkprod, hlred, hkred⟩ := h
  have hkl : k.length = l.length := by rw [← hkred, ← hlred, hkprod, hprod, hlen]
  exact hkprod.symm.trans ((congrArg (simpleWeylWord b) (hk.eq_of_length hkl)).trans hprod)

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- The equality is

```lean
u = v
```
-/
theorem WeylBruhatLE.antisymm {b : P.Base} {u v : P.weylGroup}
    (huv : WeylBruhatLE b u v) (hvu : WeylBruhatLE b v u) : u = v :=
  huv.eq_of_length_eq (Nat.le_antisymm huv.length_le hvu.length_le)

/-- Inversion preserves strong Bruhat order by reversing the
subword witnesses and using inverse-length invariance. -/
theorem WeylBruhatLE.inv {b : P.Base} {u v : P.weylGroup}
    (h : WeylBruhatLE b u v) : WeylBruhatLE b u⁻¹ v⁻¹ := by
  obtain ⟨l, k, hk, hprod, hkprod, hlred, hkred⟩ := h
  refine ⟨l.reverse, k.reverse, hk.reverse, ?_, ?_, ?_, ?_⟩
  · rw [simpleWeylWord_reverse, hprod]
  · rw [simpleWeylWord_reverse, hkprod]
  · simpa only [simpleWeylWord_reverse, rootInversionCount_inv, List.length_reverse] using hlred
  · simpa only [simpleWeylWord_reverse, rootInversionCount_inv, List.length_reverse] using hkred

/-- The equivalence is

```lean
WeylBruhatLE b u⁻¹ v⁻¹ ↔ WeylBruhatLE b u v
```
-/
@[simp] theorem weylBruhatLE_inv_iff (b : P.Base) (u v : P.weylGroup) :
    WeylBruhatLE b u⁻¹ v⁻¹ ↔ WeylBruhatLE b u v :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩

/-- Every prefix of a reduced word is reduced. -/
theorem RootInversionCount.prefix_of_reduced_append (b : P.Base)
    (l k : List b.support)
    (hred : rootInversionCount b (simpleWeylWord b (l ++ k)) = (l ++ k).length) :
    rootInversionCount b (simpleWeylWord b l) = l.length := by
  have hbound := rootInversionCount_mul_simpleWeylWord_le b (simpleWeylWord b l) k
  have hle := RootInversionCount.simpleWeylWord_le_length b l
  rw [simpleWeylWord_append, List.length_append] at hred
  omega

/-- Booleanity descends under ordinary strong Bruhat order by taking a
reduced subword of the chosen distinct-letter reduced expression. -/
theorem weyl_boolean_of_bruhatLE (b : P.Base) {u v : P.weylGroup}
    (h : WeylBruhatLE b u v)
    (hv : ∃ l : List b.support, (weylCoxeterSystem b).IsReduced l ∧
      (weylCoxeterSystem b).wordProd l = v ∧ l.Nodup) :
    ∃ k : List b.support, (weylCoxeterSystem b).IsReduced k ∧
      (weylCoxeterSystem b).wordProd k = u ∧ k.Nodup := by
  obtain ⟨l, hl, hprod, hnodup⟩ := hv
  have hlred := (weylCoxeterSystem_isReduced_iff b l).mp hl
  rw [weylCoxeterSystem_wordProd] at hprod
  rw [← hprod] at h
  obtain ⟨k, hk, hkprod, hkred⟩ := (weylBruhatLE_iff_subword b u l hlred).mp h
  exact ⟨k, (weylCoxeterSystem_isReduced_iff b k).mpr hkred,
    by simpa only [weylCoxeterSystem_wordProd] using hkprod, hnodup.sublist hk⟩

end ReductiveGroups
