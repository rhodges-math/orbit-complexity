import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PushoutProducts
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Pushout Factors

Finite arrays retain product factors for all pushout squares in finite diagrams.
-/

open CategoryTheory CategoryTheory.Limits

namespace FrobeniusSplitting

universe u v w t

private structure DiagramSquare (C : Type v) [Category.{w} C] where
  base : C
  left : C
  right : C
  apex : C
  f : base ⟶ left
  g : base ⟶ right
  p : left ⟶ apex
  q : right ⟶ apex

private instance {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] : Finite (DiagramSquare C) := by
  let tuples := Σ i : C, Σ j : C, Σ k : C, Σ l : C,
    (i ⟶ j) × (i ⟶ k) × (j ⟶ l) × (k ⟶ l)
  let encode : DiagramSquare C → tuples := fun s ↦
    ⟨s.base, s.left, s.right, s.apex, s.f, s.g, s.p, s.q⟩
  let inv : tuples → DiagramSquare C := fun ⟨i, j, k, l, f, g, p, q⟩ ↦
    ⟨i, j, k, l, f, g, p, q⟩
  have hi : Function.LeftInverse inv encode := by intro s; cases s; rfl
  exact Finite.of_injective encode hi.injective

/-- Finite diagram elements have product witnesses in finite arrays for all pushout squares. -/
theorem exists_finite_pushout_factors {C : Type v} [Category.{w} C] [Finite C]
    [∀ i j : C, Finite (i ⟶ j)] {K : Type u} [CommRing K]
    (D : C ⥤ CommAlgCat.{u} K) (V : C → Type t) [∀ i, Finite (V i)]
    (values : ∀ i, V i → D.obj i) :
    ∃ (J : C → Type (max v w t)) (_ : ∀ i, Finite (J i))
      (elements : ∀ i, J i → D.obj i),
      ∀ (i j k l : C) (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
        IsPushout (CommRingCat.ofHom (D.map f).hom.toRingHom)
          (CommRingCat.ofHom (D.map g).hom.toRingHom)
          (CommRingCat.ofHom (D.map p).hom.toRingHom)
          (CommRingCat.ofHom (D.map q).hom.toRingHom) →
        ∃ (n : V l → ℕ) (x : ∀ z, Fin (n z) → D.obj j)
          (y : ∀ z, Fin (n z) → D.obj k),
          (∀ z, values l z = ∑ a, (D.map p).hom (x z a) * (D.map q).hom (y z a)) ∧
          (∀ z a, x z a ∈ Set.range (elements j)) ∧
          ∀ z a, y z a ∈ Set.range (elements k) := by
  classical
  let squares := {s : DiagramSquare C // IsPushout
    (CommRingCat.ofHom (D.map s.f).hom.toRingHom)
    (CommRingCat.ofHom (D.map s.g).hom.toRingHom)
    (CommRingCat.ofHom (D.map s.p).hom.toRingHom)
    (CommRingCat.ofHom (D.map s.q).hom.toRingHom)}
  choose n x y hxy using fun (s : squares) (z : V s.val.apex) ↦
    exists_pushout_product_sum_of_hom (D.map s.val.f).hom.toRingHom
      (D.map s.val.g).hom.toRingHom (D.map s.val.p).hom.toRingHom
      (D.map s.val.q).hom.toRingHom s.property (values s.val.apex z)
  let factors := Σ s : squares, Σ z : V s.val.apex, Fin (n s z) × Bool
  let place : factors → C
    | ⟨s, _, _, false⟩ => s.val.left
    | ⟨s, _, _, true⟩ => s.val.right
  let val : ∀ z : factors, D.obj (place z)
    | ⟨s, z, a, false⟩ => x s z a
    | ⟨s, z, a, true⟩ => y s z a
  let J (i : C) := {z : factors // place z = i}
  let elements (i : C) (a : J i) : D.obj i := a.property ▸ val a.val
  refine ⟨J, (fun _ ↦ inferInstance), elements, ?_⟩
  intro i j k l f g p q hpush
  let s : squares := ⟨⟨i, j, k, l, f, g, p, q⟩, hpush⟩
  refine ⟨n s, x s, y s, hxy s, ?_, ?_⟩
  · intro z a
    exact ⟨⟨⟨s, z, a, false⟩, rfl⟩, rfl⟩
  · intro z a
    exact ⟨⟨⟨s, z, a, true⟩, rfl⟩, rfl⟩

end FrobeniusSplitting
