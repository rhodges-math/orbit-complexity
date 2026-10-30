import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RightmostCoefficient
import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FixedModelComparison
import Mathlib.RingTheory.Flat.Stability

/-! # The unpowered rightmost-frame equations on the prescribed arithmetic models

The chart is the original opposite-unipotent endpoint lift followed by
its original flag frame. Only its three degree-two coefficients are
retained. The single coefficient extension and every integer power are chosen
before residue primes; any previously retained full Borel character remains
on the scalar extension of the same prescribed model diagram.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct
noncomputable section
universe u v

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def framePullback (A : CommAlgCat K)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (g : G.points) : G.coordinateAlgebra →+* A :=
  (Spec.preimage (show Spec (.of A) ⟶ Spec (.of G.coordinateAlgebra) from
    (a ≫ flagChartMap G g).left)).hom

private def framePolynomial (i : G.rootBase.support) (A : CommAlgCat K)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (g : G.points) : Polynomial A :=
  Polynomial.map (framePullback G A a g)
    (simpleFramePolynomial G i (positiveDetCoefficient G))

private theorem frame_degree (i : G.rootBase.support) (A : CommAlgCat K)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (g : G.points) : (framePolynomial G i A a g).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans (simpleFrame_degree G i)

private theorem frame_top (i : G.rootBase.support) (A : CommAlgCat K)
    (a : (algSpec (.of K)).obj (.op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (g : G.points) :
    (framePolynomial G i A a g).coeff 2 = framePullback G A a g (positiveDetCoefficient G) := by
  rw [framePolynomial, Polynomial.coeff_map, simpleFrame_top]

private def quadratic {A : Type*} [Semiring A] (b : Fin 3 → A) : Polynomial A :=
  Polynomial.monomial 0 (b 0) + Polynomial.monomial 1 (b 1) +
    Polynomial.monomial 2 (b 2)

private theorem quadratic_degree {A : Type*} [Semiring A] (b : Fin 3 → A) :
    (quadratic b).natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 : 0 ≠ n := by omega
  have h1 : 1 ≠ n := by omega
  have h2 : 2 ≠ n := by omega
  simp only [quadratic, Polynomial.coeff_add, Polynomial.coeff_monomial,
    ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, add_zero]

private theorem quadratic_expansion {A : Type*} [Semiring A]
    (f : Polynomial A) (h : f.natDegree ≤ 2) :
    quadratic (fun k : Fin 3 ↦ f.coeff k) = f := by
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp [quadratic, Polynomial.coeff_monomial]
  · have hgt : 2 < n := by omega
    have h0 : 0 ≠ n := by omega
    have h1 : 1 ≠ n := by omega
    have h2 : 2 ≠ n := by omega
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero.mp h n hgt]
    simp only [quadratic, Polynomial.coeff_add, Polynomial.coeff_monomial,
      ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, add_zero]

private theorem quadratic_map {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (b : Fin 3 → A) :
    Polynomial.map f (quadratic b) = quadratic (fun k ↦ f (b k)) := by
  simp only [quadratic, Polynomial.map_add, Polynomial.map_monomial]

/-- One extension of the prescribed arithmetic diagram retains the
unpowered frame polynomials, their degree-two reset and every power.
The input frame is the original regular opposite-unipotent chart lift, not
an assumed polynomial-degree or operator-compatibility statement. -/
theorem exists_retained_frame_polynomials {J : Type v} [Finite J]
    (i : G.rootBase.support) (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (M.obj s)] [∀ s, Algebra.Smooth S (M.obj s)]
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (g : {s : Finset J // s.Nonempty} → G.points)
    (a : ∀ s : {s : Finset J // s.Nonempty},
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (oppositeUnipotentVariety G).toOver) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) M
      ∃ v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
          F ⋙ forget₂ (CommAlgCat K) CommRingCat,
        R.FG ∧
        (∀ s x, (v.app s).hom x = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M.obj s)) x)) ∧
        (∀ s, Function.Injective (v.app s).hom) ∧
        ∃ P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s),
          ∀ s,
            (P s).natDegree ≤ 2 ∧
            Polynomial.map (v.app s).hom (P s) =
              Polynomial.map (Spec.preimage (a s ≫ flagChartMap G (g s)).left).hom
                (simpleFramePolynomial G i (positiveDetCoefficient G)) ∧
            (v.app s).hom ((P s).coeff 2) =
              (Spec.preimage (a s ≫ flagChartMap G (g s)).left).hom
                (positiveDetCoefficient G) ∧
            ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n := by
  classical
  let C := {s : Finset J // s.Nonempty}
  let vars (s : C) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M.obj s))
  let rels (s : C) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M.obj s))
  let Q (s : C) : Algebra.Presentation S (M.obj s) (vars s) (rels s) :=
    Algebra.Presentation.ofFinitePresentation S (M.obj s)
  let values (s : C) (k : Fin 3) := (framePolynomial G i (F.obj s) (a s) (g s)).coeff k
  let noSrc : Empty → C := Empty.elim
  let noMaps : ∀ b : Empty, F.obj (noSrc b) →ₐ[K] F.obj (noSrc b) := fun b ↦ nomatch b
  obtain ⟨R, hSR, _, hR, _, hvalues⟩ := exists_chosen_graph_elements S hS
    (fun s : C ↦ M.obj s) (fun s : C ↦ F.obj s) e vars rels Q
    noSrc noSrc noMaps (fun _ ↦ Fin 3) values
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N := fixedFibreDiagram (R := R) (M := R) M
  let eR : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s := fun s ↦
    (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans (e s)
  obtain ⟨heR, hvalue⟩ := fixed_model_comparison (R := R) M F e he
  let v := modelEvaluation N F eR heR
  have hv (s : C) (x : N.obj s) : (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M.obj s)) x) := hvalue s x
  have hi (s : C) : Function.Injective (v.app s).hom := by
    let : Module.Flat S (M.obj s) := inferInstance
    let : Module.Flat R (N.obj s) := by
      change Module.Flat R (R ⊗[S] M.obj s)
      infer_instance
    change Function.Injective (fun x : N.obj s ↦ eR s ((1 : K) ⊗ₜ[R] x))
    exact (eR s).injective.comp
      (Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := N.obj s)
        (show Function.Injective (algebraMap R K) from Subtype.val_injective))
  have helts (s : C) (k : Fin 3) :
      ∃ x : N.obj s, (v.app s).hom x = values s k := by
    obtain ⟨x, hx⟩ := hvalues s k
    exact ⟨x, (hv s x).trans hx⟩
  let b (s : C) (k : Fin 3) : N.obj s := (helts s k).choose
  have hb (s : C) (k : Fin 3) : (v.app s).hom (b s k) = values s k :=
    (helts s k).choose_spec
  let P (s : C) := quadratic (b s)
  have hmap (s : C) : Polynomial.map (v.app s).hom (P s) =
      framePolynomial G i (F.obj s) (a s) (g s) := by
    rw [show P s = quadratic (b s) from rfl, quadratic_map]
    have hb' : (fun k : Fin 3 ↦ (v.app s).hom (b s k)) = values s := by
      funext k
      exact hb s k
    rw [hb']
    exact quadratic_expansion _ (SchubertGeometry.DeterminantSection.frame_degree G i (F.obj s) (a
      s) (g s))
  refine ⟨R, hSR, v, hR, hv, hi, P, ?_⟩
  intro s
  refine ⟨quadratic_degree (b s), hmap s, ?_, ?_⟩
  · have h := congrArg (fun f : Polynomial (F.obj s) ↦ f.coeff 2) (hmap s)
    rw [Polynomial.coeff_map, SchubertGeometry.DeterminantSection.frame_top] at h
    exact h
  · intro n
    simpa only [Nat.mul_comm] using
      (Polynomial.coeff_pow_of_natDegree_le (m := n) (quadratic_degree (b s)))

end SchubertGeometry.DeterminantSection
