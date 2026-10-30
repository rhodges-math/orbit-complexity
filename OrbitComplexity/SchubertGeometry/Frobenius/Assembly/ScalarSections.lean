import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Batteries.Tactic.Lint

/-! # Sections on prescribed scalar models

Two Cartesian scalar comparisons carry a section and its projection to the
prescribed new schemes. The section remains a closed immersion. Equations
for a local section follow from its two original projections.
-/

set_option autoImplicit false

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry

private theorem scalar_section_data {C : Type u} [Category.{v} C]
    {B X S BT XT T : C} (base : B ⟶ S) (baseX : X ⟶ S)
    (π : X ⟶ B) (δ : B ⟶ X) (hδ : δ ≫ π = 𝟙 B)
    (hbase : π ≫ base = baseX) (b : BT ⟶ B) (x : XT ⟶ X)
    (baseBT : BT ⟶ T) (baseXT : XT ⟶ T) (t : T ⟶ S)
    (hb : IsPullback b baseBT base t) (hx : IsPullback x baseXT baseX t) :
    ∃ (πT : XT ⟶ BT) (δT : BT ⟶ XT),
      δT ≫ πT = 𝟙 BT ∧ πT ≫ b = x ≫ π ∧ πT ≫ baseBT = baseXT ∧
      δT ≫ x = b ≫ δ ∧ δT ≫ baseXT = baseBT ∧
      IsPullback x πT π b ∧ IsPullback b δT δ x := by
  have hπ : (x ≫ π) ≫ base = baseXT ≫ t := by
    rw [Category.assoc, hbase]
    exact hx.w
  have hδbase : δ ≫ baseX = base := by
    rw [← hbase, ← Category.assoc, hδ, Category.id_comp]
  have hδ' : (b ≫ δ) ≫ baseX = baseBT ≫ t := by
    rw [Category.assoc, hδbase]
    exact hb.w
  let πT := hb.lift (x ≫ π) baseXT hπ
  let δT := hx.lift (b ≫ δ) baseBT hδ'
  have hπb : πT ≫ b = x ≫ π := hb.lift_fst _ _ _
  have hπbase : πT ≫ baseBT = baseXT := hb.lift_snd _ _ _
  have hδx : δT ≫ x = b ≫ δ := hx.lift_fst _ _ _
  have hδnew : δT ≫ baseXT = baseBT := hx.lift_snd _ _ _
  have hsection : δT ≫ πT = 𝟙 BT := by
    apply hb.hom_ext
    · calc
        (δT ≫ πT) ≫ b = δT ≫ (x ≫ π) := by rw [Category.assoc, hπb]
        _ = (b ≫ δ) ≫ π := by rw [← Category.assoc, hδx]
        _ = b := by rw [Category.assoc, hδ, Category.comp_id]
        _ = (𝟙 BT) ≫ b := (Category.id_comp b).symm
    · calc
        (δT ≫ πT) ≫ baseBT = δT ≫ baseXT := by rw [Category.assoc, hπbase]
        _ = baseBT := hδnew
        _ = (𝟙 BT) ≫ baseBT := (Category.id_comp baseBT).symm
  have hpull : IsPullback x πT π b := by
    have houter : IsPullback x (πT ≫ baseBT) (π ≫ base) t := by
      rw [hπbase, hbase]
      exact hx
    exact houter.of_bot hπb.symm hb
  have hspull : IsPullback b δT δ x := by
    have houter : IsPullback b (δT ≫ baseXT) (δ ≫ baseX) t := by
      rw [hδnew, hδbase]
      exact hb
    exact houter.of_bot hδx.symm hx
  exact ⟨πT, δT, hsection, hπb, hπbase, hδx, hδnew, hpull, hspull⟩

/-- A closed section and its projection extend to the prescribed Cartesian
scalar models, retaining both projections and both Cartesian squares. -/
theorem exists_scalar_section {B X S BT XT T : Scheme.{u}}
    (base : B ⟶ S) (baseX : X ⟶ S)
    (π : X ⟶ B) (δ : B ⟶ X) [IsClosedImmersion δ]
    (hδ : δ ≫ π = 𝟙 B) (hbase : π ≫ base = baseX)
    (b : BT ⟶ B) (x : XT ⟶ X) (baseBT : BT ⟶ T) (baseXT : XT ⟶ T)
    (t : T ⟶ S) (hb : IsPullback b baseBT base t)
    (hx : IsPullback x baseXT baseX t) :
    ∃ (πT : XT ⟶ BT) (δT : BT ⟶ XT),
      δT ≫ πT = 𝟙 BT ∧ IsClosedImmersion δT ∧
      πT ≫ b = x ≫ π ∧ πT ≫ baseBT = baseXT ∧
      δT ≫ x = b ≫ δ ∧ δT ≫ baseXT = baseBT ∧
      IsPullback x πT π b ∧ IsPullback b δT δ x := by
  obtain ⟨πT, δT, hsection, hπb, hπbase, hδx, hδbase, hpull, hspull⟩ :=
    scalar_section_data base baseX π δ hδ hbase b x baseBT baseXT t hb hx
  have hclosed : IsClosedImmersion δT :=
    MorphismProperty.of_isPullback hspull inferInstance
  exact ⟨πT, δT, hsection, hclosed, hπb, hπbase, hδx, hδbase, hpull, hspull⟩

/-- A scalar section has the specified local section and projection equations
whenever the old charts and the new charts retain their two projections. -/
theorem scalar_section_node {C : Type u} [Category.{v} C]
    {B X S BT XT T P A Q D : C}
    (base : B ⟶ S) (baseX : X ⟶ S) (π : X ⟶ B) (δ : B ⟶ X)
    (b : BT ⟶ B) (x : XT ⟶ X) (baseBT : BT ⟶ T) (baseXT : XT ⟶ T)
    (t : T ⟶ S) (hb : IsPullback b baseBT base t)
    (hx : IsPullback x baseXT baseX t)
    (πT : XT ⟶ BT) (δT : BT ⟶ XT)
    (hπb : πT ≫ b = x ≫ π) (hπbase : πT ≫ baseBT = baseXT)
    (hδx : δT ≫ x = b ≫ δ) (hδbase : δT ≫ baseXT = baseBT)
    (p : P ⟶ A) (s : A ⟶ P) (p₀ : Q ⟶ D) (s₀ : D ⟶ Q)
    (f : P ⟶ Q) (g : A ⟶ D)
    (k : P ⟶ XT) (k₀ : Q ⟶ X) (a : A ⟶ BT) (a₀ : D ⟶ B)
    (hps : s ≫ p = 𝟙 A) (hp : f ≫ p₀ = p ≫ g)
    (hs : s ≫ f = g ≫ s₀) (hπ₀ : k₀ ≫ π = p₀ ≫ a₀)
    (hδ₀ : s₀ ≫ k₀ = a₀ ≫ δ) (hk : k ≫ x = f ≫ k₀)
    (hkbase : k ≫ baseXT = p ≫ a ≫ baseBT) (ha : a ≫ b = g ≫ a₀) :
    p ≫ a = k ≫ πT ∧ s ≫ k = a ≫ δT := by
  constructor
  · apply hb.hom_ext
    · calc
        (p ≫ a) ≫ b = (p ≫ g) ≫ a₀ := by rw [Category.assoc, ha, ← Category.assoc]
        _ = (f ≫ p₀) ≫ a₀ := congrArg (fun h => h ≫ a₀) hp.symm
        _ = (f ≫ k₀) ≫ π := by rw [Category.assoc, ← hπ₀, ← Category.assoc]
        _ = (k ≫ πT) ≫ b := by
          symm
          rw [Category.assoc, hπb, ← Category.assoc, hk]
    · calc
        (p ≫ a) ≫ baseBT = k ≫ baseXT := by rw [Category.assoc, hkbase]
        _ = (k ≫ πT) ≫ baseBT := by rw [Category.assoc, hπbase]
  · apply hx.hom_ext
    · calc
        (s ≫ k) ≫ x = (s ≫ f) ≫ k₀ := by rw [Category.assoc, hk, ← Category.assoc]
        _ = (g ≫ s₀) ≫ k₀ := congrArg (fun h => h ≫ k₀) hs
        _ = (a ≫ b) ≫ δ := by rw [Category.assoc, hδ₀, ← Category.assoc, ← ha]
        _ = (a ≫ δT) ≫ x := (Category.assoc a b δ).trans
          (((Category.assoc a δT x).trans (congrArg (fun f => a ≫ f) hδx)).symm)
    · calc
        (s ≫ k) ≫ baseXT = (s ≫ p) ≫ a ≫ baseBT := by
          rw [Category.assoc, hkbase, ← Category.assoc s p]
        _ = a ≫ baseBT := by rw [hps, Category.id_comp]
        _ = (a ≫ δT) ≫ baseXT := by rw [Category.assoc, hδbase]

end SchubertGeometry
