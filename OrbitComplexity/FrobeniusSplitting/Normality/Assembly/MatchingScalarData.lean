import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import Mathlib.Algebra.Polynomial.Eval.Degree
import Batteries.Tactic.Lint

/-! # Matching units and quadratic coefficients under scalar maps

A natural map of coefficient diagrams transports the matching cocycle and
the quadratic leading-coefficient relation. Polynomial powers and all their
coefficients commute with the same maps.
-/

open CategoryTheory

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

namespace FrobeniusSplitting.RetainedCharacter

universe u

variable {S R J : Type u} [CommRing S] [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (μ : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat R) CommRingCat)

private theorem scalar_natural_apply
    (s t : {s : Finset J // s.Nonempty}) (f : s ⟶ t) (a : N.obj s) :
    (μ.app t).hom ((N.map f).hom a) =
      (M.map f).hom ((μ.app s).hom a) :=
  congrArg (fun g : CommRingCat.of (N.obj s) ⟶ CommRingCat.of (M.obj t) ↦ g.hom a)
    (μ.naturality f)

/-- The matching transition units mapped into the new coefficient diagram. -/
def matchingScalarUnits
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) : (M.obj s)ˣ :=
  Units.map (μ.app s).hom.toMonoidHom (delta s j hj k hk)

/-- The quadratic on a singleton chart with its coefficients mapped. -/
noncomputable def matchingScalarPolynomial
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) (j : J) :
    Polynomial (M.obj (singletonIndex j)) :=
  Polynomial.map (μ.app (singletonIndex j)).hom (P j)

/-- The matching cocycle equation survives every natural coefficient map. -/
theorem matchingScalarUnits_cocycle
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk) :
    ∀ s j hj k hk l hl,
      matchingScalarUnits N M μ delta s j hj l hl =
        matchingScalarUnits N M μ delta s k hk l hl *
          matchingScalarUnits N M μ delta s j hj k hk := by
  intro s j hj k hk l hl
  simpa only [matchingScalarUnits, map_mul] using
    congrArg (Units.map (μ.app s).hom.toMonoidHom) (hco s j hj k hk l hl)

/-- The mapped transition units retain their refinement equation. -/
theorem matchingScalarUnits_natural
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (M.map f).hom.toMonoidHom
        (matchingScalarUnits N M μ delta s j hj k hk) =
          matchingScalarUnits N M μ delta t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
  intro s t f j hj k hk
  apply Units.ext
  change (M.map f).hom ((μ.app s).hom (delta s j hj k hk : N.obj s)) =
    (μ.app t).hom (delta t j ((leOfHom f) hj) k ((leOfHom f) hk) : N.obj t)
  rw [← scalar_natural_apply N M μ s t f]
  exact congrArg (μ.app t).hom (congrArg Units.val (hn s t f j hj k hk))

/-- Coefficient mapping preserves the degree bound of the retained quadratic. -/
theorem matchingScalarPolynomial_degree
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hP : ∀ j, (P j).natDegree ≤ 2) (j : J) :
    (matchingScalarPolynomial N M μ P j).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans (hP j)

/-- The quadratic leading coefficients retain their matching-unit relation. -/
theorem matchingScalarPolynomial_leading
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) *
          (delta s j hj k hk : N.obj s)) :
    ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (M.map (singletonArrow s j hj)).hom
          ((matchingScalarPolynomial N M μ P j).coeff 2) =
        (M.map (singletonArrow s k hk)).hom
            ((matchingScalarPolynomial N M μ P k).coeff 2) *
          (matchingScalarUnits N M μ delta s j hj k hk : M.obj s) := by
  intro s j hj k hk
  let φ (t : {s : Finset J // s.Nonempty}) : N.obj t →+* M.obj t := (μ.app t).hom
  have hcoeff (l : J) :
      (matchingScalarPolynomial N M μ P l).coeff 2 =
        φ (singletonIndex l) ((P l).coeff 2) :=
    Polynomial.coeff_map _ _
  have hj' : (M.map (singletonArrow s j hj)).hom
      (φ (singletonIndex j) ((P j).coeff 2)) =
        φ s ((N.map (singletonArrow s j hj)).hom ((P j).coeff 2)) :=
    (scalar_natural_apply N M μ _ _ (singletonArrow s j hj) _).symm
  have hk' : (M.map (singletonArrow s k hk)).hom
      (φ (singletonIndex k) ((P k).coeff 2)) =
        φ s ((N.map (singletonArrow s k hk)).hom ((P k).coeff 2)) :=
    (scalar_natural_apply N M μ _ _ (singletonArrow s k hk) _).symm
  have hd : (matchingScalarUnits N M μ delta s j hj k hk : M.obj s) =
      φ s (delta s j hj k hk : N.obj s) := rfl
  rw [hcoeff, hcoeff, hd, hj', hk', ← map_mul]
  exact congrArg (φ s) (hr s j hj k hk)

/-- Every power of the mapped quadratic is the map of the same original power. -/
theorem matchingScalarPolynomial_pow
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) (j : J) (n : ℕ) :
    matchingScalarPolynomial N M μ P j ^ n =
      Polynomial.map (μ.app (singletonIndex j)).hom (P j ^ n) :=
  (Polynomial.map_pow _ n).symm

/-- Powers of every coefficient commute with the chosen coefficient map. -/
theorem matchingScalarPolynomial_coeff_pow
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) (j : J) (k n : ℕ) :
    (matchingScalarPolynomial N M μ P j).coeff k ^ n =
      (μ.app (singletonIndex j)).hom ((P j).coeff k ^ n) := by
  rw [matchingScalarPolynomial, Polynomial.coeff_map, map_pow]

/-- All coefficients of every polynomial power commute with coefficient mapping. -/
theorem matchingScalarPolynomial_pow_coeff
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) (j : J) (n k : ℕ) :
    (matchingScalarPolynomial N M μ P j ^ n).coeff k =
      (μ.app (singletonIndex j)).hom ((P j ^ n).coeff k) := by
  rw [matchingScalarPolynomial_pow, Polynomial.coeff_map]

end FrobeniusSplitting.RetainedCharacter
