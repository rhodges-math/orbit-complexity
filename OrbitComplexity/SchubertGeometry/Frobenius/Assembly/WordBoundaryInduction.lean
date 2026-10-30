import OrbitComplexity.SchubertGeometry.Normality.Models.BsdhInfinity
import Mathlib.Data.List.Induction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Omitted-letter morphisms in a Bott--Samelson word

Appending the same simple correspondence transports an endpoint-preserving
morphism through a Cartesian square. This defines all omitted-letter maps
from the last-letter section.
-/

set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions

open private append_ext from OrbitComplexity.SchubertGeometry.Normality.Models.BsdhInfinity

namespace SchubertGeometry

private def appendPullbackMap {D : Type u} [Category.{v} D]
    {A B E T : D} (f : A ⟶ T) (g : B ⟶ T) (h : E ⟶ T)
    [HasPullback f h] [HasPullback g h] (a : A ⟶ B) (ha : a ≫ g = f) :
    pullback f h ⟶ pullback g h :=
  pullback.lift (pullback.fst f h ≫ a) (pullback.snd f h) (by
    rw [Category.assoc, ha, pullback.condition])

private theorem appendPullbackMap_fst {D : Type u} [Category.{v} D]
    {A B E T : D} (f : A ⟶ T) (g : B ⟶ T) (h : E ⟶ T)
    [HasPullback f h] [HasPullback g h] (a : A ⟶ B) (ha : a ≫ g = f) :
    appendPullbackMap f g h a ha ≫ pullback.fst g h = pullback.fst f h ≫ a := by
  simp only [appendPullbackMap, pullback.lift_fst]

private theorem appendPullbackMap_snd {D : Type u} [Category.{v} D]
    {A B E T : D} (f : A ⟶ T) (g : B ⟶ T) (h : E ⟶ T)
    [HasPullback f h] [HasPullback g h] (a : A ⟶ B) (ha : a ≫ g = f) :
    appendPullbackMap f g h a ha ≫ pullback.snd g h = pullback.snd f h := by
  simp only [appendPullbackMap, pullback.lift_snd]

private theorem appendPullbackMap_cartesian {D : Type u} [Category.{v} D]
    {A B E T : D} (f : A ⟶ T) (g : B ⟶ T) (h : E ⟶ T)
    [HasPullback f h] [HasPullback g h] (a : A ⟶ B) (ha : a ≫ g = f) :
    IsPullback (appendPullbackMap f g h a ha) (pullback.fst f h)
      (pullback.fst g h) a := by
  apply IsPullback.of_right ?_ (appendPullbackMap_fst f g h a ha)
    (IsPullback.of_hasPullback g h).flip
  rw [appendPullbackMap_snd, ha]
  exact (IsPullback.of_hasPullback f h).flip

private theorem conjugate_cartesian {D : Type u} [Category.{v} D]
    {P Q A B X Y : D} {f : P ⟶ Q} {a : P ⟶ A} {b : Q ⟶ B} {g : A ⟶ B}
    (h : IsPullback f a b g) (eX : X ≅ P) (eY : Y ≅ Q) :
    IsPullback (eX.hom ≫ f ≫ eY.inv) (eX.hom ≫ a) (eY.hom ≫ b) g := by
  apply h.of_iso eX.symm eY.symm (Iso.refl A) (Iso.refl B) <;>
    simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.id_comp,
      Iso.inv_hom_id_assoc]

private theorem conjugate_endpoint {D : Type u} [Category.{v} D]
    {P Q X Y E T : D} (f : P ⟶ Q) (a : P ⟶ E) (b : Q ⟶ E) (t : E ⟶ T)
    (eX : X ≅ P) (eY : Y ≅ Q) (rX : X ⟶ T) (rY : Y ⟶ T)
    (hf : f ≫ b = a) (hX : eX.hom ≫ a ≫ t = rX)
    (hY : eY.hom ≫ b ≫ t = rY) :
    (eX.hom ≫ f ≫ eY.inv) ≫ rY = rX := by
  calc
    _ = eX.hom ≫ f ≫ b ≫ t := by
      rw [← hY]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = eX.hom ≫ (f ≫ b) ≫ t := by simp only [Category.assoc]
    _ = rX := by rw [hf]; exact hX

private theorem source_cartesian {D : Type u} [Category.{v} D]
    {P X A B T : D} {f : P ⟶ A} {g : P ⟶ B} {h : A ⟶ T} {k : B ⟶ T}
    (hp : IsPullback f g h k) (e : X ≅ P) :
    IsPullback (e.hom ≫ f) (e.hom ≫ g) h k := by
  apply hp.of_iso e.symm (Iso.refl A) (Iso.refl B) (Iso.refl T) <;>
    simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.id_comp,
      Iso.inv_hom_id_assoc]

private theorem cartesian_first_eq {D : Type u} [Category.{v} D]
    {P X A B : D} {f f' : P ⟶ X} {g : P ⟶ A} {h : X ⟶ B} {k : A ⟶ B}
    (hf : f = f') (hp : IsPullback f' g h k) : IsPullback f g h k := by
  cases hf
  exact hp

private theorem closed_of_cartesian {P X A B : Scheme.{u}}
    (f : P ⟶ X) (g : P ⟶ A) (h : X ⟶ B) (k : A ⟶ B)
    (hp : IsPullback f g h k) [IsClosedImmersion k] : IsClosedImmersion f := by
  rw [← hp.isoPullback_hom_fst]
  infer_instance

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private abbrev appendBundle (i : G.rootBase.support) :=
  flagBundleScheme G (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private abbrev appendProjection (i : G.rootBase.support) :
    appendBundle G i ⟶ (flagVariety G).scheme :=
  flagBundleProjection G (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private abbrev appendEndpoint (i : G.rootBase.support) :
    appendBundle G i ⟶ (flagVariety G).scheme :=
  flagBundleMap G (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))

private def appendSchemeIso (word : List G.rootBase.support) (i : G.rootBase.support) :
    bsdhScheme G (word ++ [i]) ≅ pullback (bsdhMap G word) (appendProjection G i) :=
  (Over.forget (flagVariety G).scheme).mapIso (bsdhAppendIso G word i)

/-- An endpoint-preserving word morphism extends through the appended simple
correspondence on both words. -/
def bsdhAppendMap {v w : List G.rootBase.support}
    (a : bsdhScheme G v ⟶ bsdhScheme G w) (ha : a ≫ bsdhMap G w = bsdhMap G v)
    (i : G.rootBase.support) : bsdhScheme G (v ++ [i]) ⟶ bsdhScheme G (w ++ [i]) :=
  (appendSchemeIso G v i).hom ≫
    appendPullbackMap (bsdhMap G v) (bsdhMap G w) (appendProjection G i) a ha ≫
      (appendSchemeIso G w i).inv

/-- Appending preserves the Cartesian square of the two word projections. -/
theorem bsdhAppendMap_cartesian {v w : List G.rootBase.support}
    (a : bsdhScheme G v ⟶ bsdhScheme G w) (ha : a ≫ bsdhMap G w = bsdhMap G v)
    (i : G.rootBase.support) :
    IsPullback (bsdhAppendMap G a ha i) (bsdhAppendFst G v i) (bsdhAppendFst G w i) a :=
  conjugate_cartesian
    (appendPullbackMap_cartesian (bsdhMap G v) (bsdhMap G w) (appendProjection G i) a ha)
      (appendSchemeIso G v i) (appendSchemeIso G w i)

/-- The appended word morphism preserves the final flag. -/
theorem bsdhAppendMap_endpoint {v w : List G.rootBase.support}
    (a : bsdhScheme G v ⟶ bsdhScheme G w) (ha : a ≫ bsdhMap G w = bsdhMap G v)
    (i : G.rootBase.support) :
    bsdhAppendMap G a ha i ≫ bsdhMap G (w ++ [i]) = bsdhMap G (v ++ [i]) :=
  conjugate_endpoint
    (appendPullbackMap (bsdhMap G v) (bsdhMap G w) (appendProjection G i) a ha)
    (pullback.snd (bsdhMap G v) (appendProjection G i))
    (pullback.snd (bsdhMap G w) (appendProjection G i)) (appendEndpoint G i)
    (appendSchemeIso G v i) (appendSchemeIso G w i)
    (bsdhMap G (v ++ [i])) (bsdhMap G (w ++ [i]))
    (appendPullbackMap_snd (bsdhMap G v) (bsdhMap G w) (appendProjection G i) a ha)
    (bsdhAppendIso_endpoint G v i) (bsdhAppendIso_endpoint G w i)

private theorem erase_append_before {A : Type*} (w : List A) (i : A) (n : ℕ)
    (hn : n < w.length) : (w ++ [i]).eraseIdx n = w.eraseIdx n ++ [i] := by
  induction w generalizing n with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hn
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change a :: (w ++ [i]).eraseIdx n = a :: (w.eraseIdx n ++ [i])
      exact congrArg (List.cons a) (ih n (Nat.lt_of_succ_lt_succ hn))

private theorem erase_append_last {A : Type*} (w : List A) (i : A) :
    (w ++ [i]).eraseIdx w.length = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change a :: (w ++ [i]).eraseIdx w.length = a :: w
    exact congrArg (List.cons a) ih

private def familyCast {D : Type u} [Category.{v} D] {Idx : Type*}
    (X : Idx → D) {i j : Idx} (h : i = j) : X i ⟶ X j :=
  eqToHom (congrArg X h)

private instance familyCast_isIso {D : Type u} [Category.{v} D] {Idx : Type*}
    (X : Idx → D) {i j : Idx} (h : i = j) : IsIso (familyCast X h) := by
  dsimp only [familyCast]
  infer_instance

private theorem familyCast_endpoint {D : Type u} [Category.{v} D] {Idx : Type*}
    (X : Idx → D) {T : D} (p : ∀ i, X i ⟶ T) {i j : Idx} (h : i = j) :
    familyCast X h ≫ p j = p i := by
  cases h
  exact Category.id_comp _

private def lastSection (w : List G.rootBase.support) (i : G.rootBase.support) :
    bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]) :=
  Classical.choose (bsdh_omitted_section G w i)

private theorem lastSection_closed (w : List G.rootBase.support) (i : G.rootBase.support) :
    IsClosedImmersion (lastSection G w i) :=
  (Classical.choose_spec (bsdh_omitted_section G w i)).1

private theorem lastSection_fst (w : List G.rootBase.support) (i : G.rootBase.support) :
    lastSection G w i ≫ bsdhAppendFst G w i = 𝟙 _ :=
  (Classical.choose_spec (bsdh_omitted_section G w i)).2.1

private theorem lastSection_endpoint (w : List G.rootBase.support) (i : G.rootBase.support) :
    lastSection G w i ≫ bsdhMap G (w ++ [i]) = bsdhMap G w :=
  (Classical.choose_spec (bsdh_omitted_section G w i)).2.2

private abbrev omissionType (w : List G.rootBase.support) :=
  ∀ k : Fin w.length,
    {a : bsdhScheme G (w.eraseIdx k.val) ⟶ bsdhScheme G w //
      IsClosedImmersion a ∧ a ≫ bsdhMap G w = bsdhMap G (w.eraseIdx k.val)}

private def omissionNil : omissionType G [] := fun k => Fin.elim0 k

private def chooseCase {T : Sort*} (q : Prop) [Decidable q]
    (left : q → T) (right : ¬q → T) : T :=
  if h : q then left h else right h

private theorem chooseCase_left {T : Sort*} (q : Prop) [Decidable q]
    (left : q → T) (right : ¬q → T) (h : q) :
    chooseCase q left right = left h := by
  exact dite_eq_left h

private theorem chooseCase_right {T : Sort*} (q : Prop) [Decidable q]
    (left : q → T) (right : ¬q → T) (h : ¬q) :
    chooseCase q left right = right h := by
  exact dite_eq_right h

private def omissionBeforeMap (w : List G.rootBase.support) (i : G.rootBase.support)
    (ih : omissionType G w) (n : ℕ) (hn : n < w.length) :
    bsdhScheme G ((w ++ [i]).eraseIdx n) ⟶ bsdhScheme G (w ++ [i]) :=
  familyCast (bsdhScheme G) (erase_append_before w i n hn) ≫
    bsdhAppendMap G (ih ⟨n, hn⟩).val (ih ⟨n, hn⟩).property.2 i

private theorem omissionBeforeMap_cartesian (w : List G.rootBase.support)
    (i : G.rootBase.support) (ih : omissionType G w) (n : ℕ) (hn : n < w.length) :
    IsPullback (omissionBeforeMap G w i ih n hn)
      (familyCast (bsdhScheme G) (erase_append_before w i n hn) ≫
        bsdhAppendFst G (w.eraseIdx n) i)
      (bsdhAppendFst G w i) (ih ⟨n, hn⟩).val :=
  source_cartesian
    (bsdhAppendMap_cartesian G (ih ⟨n, hn⟩).val (ih ⟨n, hn⟩).property.2 i)
    (eqToIso (congrArg (bsdhScheme G) (erase_append_before w i n hn)))

private def omissionBefore (w : List G.rootBase.support) (i : G.rootBase.support)
    (ih : omissionType G w) (k : Fin (w ++ [i]).length) (hk : k.val < w.length) :
    {a : bsdhScheme G ((w ++ [i]).eraseIdx k.val) ⟶ bsdhScheme G (w ++ [i]) //
      IsClosedImmersion a ∧ a ≫ bsdhMap G (w ++ [i]) =
        bsdhMap G ((w ++ [i]).eraseIdx k.val)} := by
  let : IsClosedImmersion (ih ⟨k.val, hk⟩).val := (ih ⟨k.val, hk⟩).property.1
  refine ⟨omissionBeforeMap G w i ih k.val hk, ?_, ?_⟩
  · exact closed_of_cartesian _ _ _ _ (omissionBeforeMap_cartesian G w i ih k.val hk)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => familyCast (bsdhScheme G)
        (erase_append_before w i k.val hk) ≫ h)
        (bsdhAppendMap_endpoint G (ih ⟨k.val, hk⟩).val
          (ih ⟨k.val, hk⟩).property.2 i)).trans
          (familyCast_endpoint (bsdhScheme G) (bsdhMap G)
            (erase_append_before w i k.val hk)))

private def omissionLast (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin (w ++ [i]).length) (hk : ¬k.val < w.length) :
    {a : bsdhScheme G ((w ++ [i]).eraseIdx k.val) ⟶ bsdhScheme G (w ++ [i]) //
      IsClosedImmersion a ∧ a ≫ bsdhMap G (w ++ [i]) =
        bsdhMap G ((w ++ [i]).eraseIdx k.val)} := by
  have hle : k.val ≤ w.length := Nat.le_of_lt_succ (by
    simpa only [List.length_append, List.length_singleton] using k.isLt)
  have heq : k.val = w.length := Nat.le_antisymm hle (Nat.le_of_not_gt hk)
  let hErase := (congrArg (fun n => (w ++ [i]).eraseIdx n) heq).trans
    (erase_append_last w i)
  let t := familyCast (bsdhScheme G) hErase
  let : IsClosedImmersion (lastSection G w i) := lastSection_closed G w i
  refine ⟨t ≫ lastSection G w i, inferInstance, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => t ≫ h) (lastSection_endpoint G w i)).trans
      (familyCast_endpoint (bsdhScheme G) (bsdhMap G) hErase))

private def omissionStep (w : List G.rootBase.support) (i : G.rootBase.support)
    (ih : omissionType G w) : omissionType G (w ++ [i]) := fun k =>
  chooseCase (k.val < w.length) (omissionBefore G w i ih k) (omissionLast G w i k)

private theorem omissionStep_before (w : List G.rootBase.support)
    (i : G.rootBase.support) (ih : omissionType G w)
    (k : Fin (w ++ [i]).length) (hk : k.val < w.length) :
    omissionStep G w i ih k = omissionBefore G w i ih k hk :=
  chooseCase_left (k.val < w.length) (omissionBefore G w i ih k)
    (omissionLast G w i k) hk

private theorem omissionStep_last (w : List G.rootBase.support)
    (i : G.rootBase.support) (ih : omissionType G w)
    (k : Fin (w ++ [i]).length) (hk : ¬k.val < w.length) :
    omissionStep G w i ih k = omissionLast G w i k hk :=
  chooseCase_right (k.val < w.length) (omissionBefore G w i ih k)
    (omissionLast G w i k) hk

private def omissionData (w : List G.rootBase.support) : omissionType G w :=
  w.reverseRecOn (omissionNil G) (omissionStep G)

private theorem omissionData_append (w : List G.rootBase.support) (i : G.rootBase.support) :
    omissionData G (w ++ [i]) = omissionStep G w i (omissionData G w) :=
  List.reverseRecOn_concat i w (omissionNil G) (omissionStep G)

/-- Inserting an identity correspondence at the indexed position is the
omitted-letter morphism into the Bott--Samelson word. -/
def bsdhOmitMap (w : List G.rootBase.support) (k : Fin w.length) :
    bsdhScheme G (w.eraseIdx k.val) ⟶ bsdhScheme G w :=
  (omissionData G w k).val

/-- Every omitted-letter morphism is a closed immersion. -/
theorem bsdhOmitMap_closed (w : List G.rootBase.support) (k : Fin w.length) :
    IsClosedImmersion (bsdhOmitMap G w k) := (omissionData G w k).property.1

/-- Omitting an identity correspondence preserves the final flag. -/
theorem bsdhOmitMap_endpoint (w : List G.rootBase.support) (k : Fin w.length) :
    bsdhOmitMap G w k ≫ bsdhMap G w = bsdhMap G (w.eraseIdx k.val) :=
  (omissionData G w k).property.2

private def priorIndex (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin w.length) : Fin (w ++ [i]).length :=
  ⟨k.val, by
    simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt k.isLt⟩

private def lastIndex (w : List G.rootBase.support) (i : G.rootBase.support) :
    Fin (w ++ [i]).length :=
  ⟨w.length, by simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _⟩

private theorem bsdhOmitMap_before (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin w.length) :
    bsdhOmitMap G (w ++ [i]) (priorIndex G w i k) =
      omissionBeforeMap G w i (omissionData G w) k.val k.isLt := by
  exact (congrArg (fun f => (f (priorIndex G w i k)).val)
    (omissionData_append G w i)).trans
      (congrArg Subtype.val
        (omissionStep_before G w i (omissionData G w) (priorIndex G w i k) k.isLt))

/-- An earlier omitted-letter map in an appended word is the Cartesian
pullback of the preceding word's omitted-letter map. -/
theorem bsdhOmitMap_cartesian (w : List G.rootBase.support) (i : G.rootBase.support)
    (k : Fin w.length) :
    IsPullback (bsdhOmitMap G (w ++ [i]) (priorIndex G w i k))
      (familyCast (bsdhScheme G) (erase_append_before w i k.val k.isLt) ≫
        bsdhAppendFst G (w.eraseIdx k.val) i)
      (bsdhAppendFst G w i) (bsdhOmitMap G w k) := by
  exact cartesian_first_eq (bsdhOmitMap_before G w i k)
    (omissionBeforeMap_cartesian G w i (omissionData G w) k.val k.isLt)

private theorem bsdhOmitMap_last (w : List G.rootBase.support) (i : G.rootBase.support) :
    bsdhOmitMap G (w ++ [i]) (lastIndex G w i) =
      familyCast (bsdhScheme G) (erase_append_last w i) ≫ lastSection G w i := by
  have h := congrArg Subtype.val
    (omissionStep_last G w i (omissionData G w) (lastIndex G w i) (Nat.lt_irrefl w.length))
  exact (congrArg (fun f => (f (lastIndex G w i)).val)
    (omissionData_append G w i)).trans h

/-- The last omitted-letter map is the section specified by its projection
and endpoint equations, independently of the choice of that section. -/
theorem bsdhOmitMap_last_eq (w : List G.rootBase.support) (i : G.rootBase.support)
    (d : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]))
    (hdπ : d ≫ bsdhAppendFst G w i = 𝟙 _)
    (hdτ : d ≫ bsdhMap G (w ++ [i]) = bsdhMap G w) :
    bsdhOmitMap G (w ++ [i]) (lastIndex G w i) =
      familyCast (bsdhScheme G) (erase_append_last w i) ≫ d := by
  have hd : lastSection G w i = d := append_ext G w i _ _
    ((lastSection_fst G w i).trans hdπ.symm)
    ((lastSection_endpoint G w i).trans hdτ.symm)
  exact (bsdhOmitMap_last G w i).trans
    (congrArg (fun f : bsdhScheme G w ⟶ bsdhScheme G (w ++ [i]) =>
      familyCast (bsdhScheme G) (erase_append_last w i) ≫ f) hd)

end SchubertGeometry
