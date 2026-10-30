import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Polynomial.Eval.Defs
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Full polynomial coordinates on intersection charts

The full singleton polynomial comparison, naturality of the coefficient
diagram, and the original chart projections determine the full polynomial
on every intersection chart. This comparison retains all coefficients.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

private theorem polynomial_square {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D)
    (h : b.comp f = g.comp a) (P : Polynomial A) :
    Polynomial.map b (Polynomial.map f P) = Polynomial.map g (Polynomial.map a P) := by
  simp only [Polynomial.map_map, h]

private theorem polynomial_spec_map {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (a : Spec (.of A) ⟶ Spec (.of C))
    (b : Spec (.of B) ⟶ Spec (.of C))
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = b) (P : Polynomial C) :
    Polynomial.map f (Polynomial.map (Spec.preimage a).hom P) =
      Polynomial.map (Spec.preimage b).hom P := by
  have hpre : Spec.preimage b = Spec.preimage a ≫ CommRingCat.ofHom f := by
    rw [← h, Spec.preimage_comp, Spec.preimage_map]
  have hring : (Spec.preimage b).hom = f.comp (Spec.preimage a).hom :=
    congrArg (fun q => q.hom) hpre
  rw [Polynomial.map_map, hring]

/-- The retained full singleton polynomial comparison extends to every
original intersection chart using the same coefficient maps and chart
projections. In particular the result identifies the whole polynomial,
including its lower coefficients. -/
theorem wordPolynomial_chart {K R C J : Type u}
    [CommRing K] [CommRing R] [CommRing C]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (Q : ∀ j, Polynomial (N.obj (singletonIndex j))) (P : Polynomial C)
    (U : J → Scheme.{u})
    (p₀ : ∀ j, Spec (.of (F.obj (singletonIndex j))) ⟶ U j)
    (a₀ : ∀ j, U j ⟶ Spec (.of C))
    (a : ∀ j, Spec (.of (F.obj (singletonIndex j))) ⟶ Spec (.of C))
    (ha : ∀ j, a j = p₀ j ≫ a₀ j)
    (ps : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      Spec (.of (F.obj s)) ⟶ U j)
    (hps : ∀ s j hj, Spec.map (CommRingCat.ofHom
      (F.map (singletonArrow s j hj)).hom.toRingHom) ≫ p₀ j = ps s j hj)
    (hQ : ∀ j, Polynomial.map (v.app (singletonIndex j)).hom (Q j) =
      Polynomial.map (Spec.preimage (a j)).hom P) :
    ∀ s j hj, Polynomial.map (v.app s).hom
      (Polynomial.map (N.map (singletonArrow s j hj)).hom.toRingHom (Q j)) =
        Polynomial.map (Spec.preimage (ps s j hj ≫ a₀ j)).hom P := by
  intro s j hj
  have hnat : (v.app s).hom.comp (N.map (singletonArrow s j hj)).hom.toRingHom =
      (F.map (singletonArrow s j hj)).hom.toRingHom.comp
        (v.app (singletonIndex j)).hom :=
    congrArg (fun f => f.hom) (v.naturality (singletonArrow s j hj))
  have hchart : Spec.map (CommRingCat.ofHom
      (F.map (singletonArrow s j hj)).hom.toRingHom) ≫ a j = ps s j hj ≫ a₀ j := by
    rw [ha j, ← Category.assoc, hps s j hj]
  calc
    _ = Polynomial.map (F.map (singletonArrow s j hj)).hom.toRingHom
        (Polynomial.map (v.app (singletonIndex j)).hom (Q j)) :=
      polynomial_square _ _ _ _ hnat (Q j)
    _ = Polynomial.map (F.map (singletonArrow s j hj)).hom.toRingHom
        (Polynomial.map (Spec.preimage (a j)).hom P) :=
      congrArg (Polynomial.map (F.map (singletonArrow s j hj)).hom.toRingHom) (hQ j)
    _ = _ := polynomial_spec_map _ _ _ hchart P

end SchubertGeometry.RetainedCharacter
