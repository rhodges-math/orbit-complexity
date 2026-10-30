import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Flat.Basic
import Batteries.Tactic.Lint

/-! # Retaining the units between affine line coframes

Two coframes of a line determine an automorphism of the unit module. Its value
at one and the value of its inverse give a unit in the affine coordinate ring.
Finitely many such units and their inverses are retained in scalar extensions
of the specified presentation models, before taking any powers.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

noncomputable section
universe u v w

namespace FrobeniusSplitting

private theorem linear_self_value {A : Type u} [CommRing A]
    (f : A →ₗ[A] A) (x : A) : f x = x * f 1 := by
  simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : A)

private def linearFrameUnit {A : Type u} [CommRing A] (e : A ≃ₗ[A] A) : Aˣ := by
  have hinv : e.symm 1 * e 1 = 1 :=
    (linear_self_value e.toLinearMap (e.symm 1)).symm.trans (e.apply_symm_apply 1)
  exact Units.mkOfMulEqOne (e 1) (e.symm 1) ((mul_comm _ _).trans hinv)

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def unitTopEquiv {X : Scheme.{u}} (e : unitModule X ≅ unitModule X) :
    Γ(X, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) where
  toLinearMap := (e.hom.val.app (op ⊤)).hom
  invFun := (e.inv.val.app (op ⊤)).hom
  left_inv s := congrArg
    (fun k : unitModule X ⟶ unitModule X => (k.val.app (op ⊤)).hom s) e.hom_inv_id
  right_inv s := congrArg
    (fun k : unitModule X ⟶ unitModule X => (k.val.app (op ⊤)).hom s) e.inv_hom_id

/-- The coordinate unit comparing two affine coframes is obtained from their
ratio automorphism of the unit module. -/
def affineCoframeUnit (A : Type u) [CommRing A]
    {L : (Spec (.of A)).Modules} (e f : L ≅ unitModule (Spec (.of A))) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (.of A)).hom.hom.toMonoidHom
    (linearFrameUnit (unitTopEquiv (e.symm ≪≫ f)))

/-- The comparing unit is the coordinate value of the second coframe on the
inverse image of one under the first coframe. -/
theorem affineCoframeUnit_value (A : Type u) [CommRing A]
    {L : (Spec (.of A)).Modules} (e f : L ≅ unitModule (Spec (.of A))) :
    (affineCoframeUnit A e f : A) =
      (Scheme.ΓSpecIso (.of A)).hom
        ((f.hom.val.app (op ⊤)).hom
          ((e.inv.val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤)))) := rfl

private theorem scalarEvaluation_injective
    {S R K M A : Type u} [CommRing S] [CommRing R] [CommRing K]
    [CommRing M] [CommRing A]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    [Algebra S M] [Module.Flat S M] [Algebra K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (fun x : R ⊗[S] M => e
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S M) x)) := by
  apply e.injective.comp
  change Function.Injective ((IsScalarTower.toAlgHom S R K).toLinearMap.rTensor M)
  exact Module.Flat.rTensor_preserves_injective_linearMap _ hi

private theorem lift_unit_family {I : Type v} {M A : I → Type u}
    [∀ i, CommRing (M i)] [∀ i, CommRing (A i)]
    (v : ∀ i, M i →+* A i) (hv : ∀ i, Function.Injective (v i))
    (c : ∀ i, (A i)ˣ)
    (hc : ∀ i, (∃ x, v i x = (c i : A i)) ∧
      ∃ y, v i y = (↑((c i)⁻¹) : A i)) :
    ∃ d : ∀ i, (M i)ˣ,
      (∀ i, v i (d i : M i) = (c i : A i)) ∧
      ∀ (i : I) (n : ℕ), v i ((d i : M i) ^ n) = (c i : A i) ^ n := by
  classical
  choose x hx using fun i => (hc i).1
  choose y hy using fun i => (hc i).2
  have hxy (i : I) : x i * y i = 1 := by
    apply hv i
    exact (map_mul (v i) (x i) (y i)).trans
      ((congrArg₂ (· * ·) (hx i) (hy i)).trans
        ((c i).mul_inv.trans (map_one (v i)).symm))
  let d (i : I) : (M i)ˣ := Units.mkOfMulEqOne (x i) (y i) (hxy i)
  refine ⟨d, hx, ?_⟩
  intro i n
  exact (map_pow (v i) (d i : M i) n).trans
    (congrArg (fun a : A i => a ^ n) (hx i))

/-- One coefficient extension retains a family of affine coframe units in the
specified tensor models, together with every power of the same units. -/
def frameUnitStage {K : Type u} [Field K] (S : Subalgebra ℤ K)
    {I : Type v} (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (c : ∀ i, (A i)ˣ)
    (R : Subalgebra ℤ K) (hSR : S ≤ R) : Prop :=
  letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  R.FG ∧ ∃ d : ∀ i, (R ⊗[S] M i)ˣ,
    (∀ i, e i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
      (AlgHom.id S (M i)) (d i : R ⊗[S] M i)) = (c i : A i)) ∧
    ∀ (i : I) (n : ℕ), e i (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
      (AlgHom.id S (M i)) ((d i : R ⊗[S] M i) ^ n)) = (c i : A i) ^ n

private theorem exists_unit_stage {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, Module.Flat S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (vars rels : I → Type w) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (Q : ∀ i, Algebra.Presentation S (M i) (vars i) (rels i))
    (c : ∀ i, (A i)ˣ) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R), frameUnitStage S M A e c R hSR := by
  let values (i : I) : Fin 2 → A i :=
    Fin.cases (c i : A i) (fun _ => (↑((c i)⁻¹) : A i))
  obtain ⟨R, hSR, _arrows, hR, _harrows, helts⟩ :=
    exists_chosen_graph_elements S hS (J := Empty) M A e vars rels Q
      (fun b : Empty => b.elim) (fun b : Empty => b.elim)
      (fun b : Empty => b.elim) (fun _ : I => Fin 2) values
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let v (i : I) : R ⊗[S] M i →+* A i :=
    (e i).toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K) (AlgHom.id S (M i))).toRingHom
  have hv (i : I) : Function.Injective (v i) :=
    scalarEvaluation_injective (e i) (FaithfulSMul.algebraMap_injective R K)
  have hc (i : I) : (∃ x, v i x = (c i : A i)) ∧
      ∃ y, v i y = (↑((c i)⁻¹) : A i) := by
    exact ⟨helts i 0, helts i 1⟩
  obtain ⟨d, hd, hpowers⟩ := lift_unit_family v hv c hc
  exact ⟨R, hSR, hR, d, hd, hpowers⟩

/-- The ratios of finitely many pairs of affine line coframes descend as units
on scalar extensions of the fixed presentation models, before all powers. -/
theorem exists_frame_unit_retention {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (M A : I → Type u)
    [∀ i, CommRing (M i)] [∀ i, Algebra S (M i)]
    [∀ i, Module.Flat S (M i)]
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i)
    (vars rels : I → Type w) [∀ i, Finite (vars i)] [∀ i, Finite (rels i)]
    (Q : ∀ i, Algebra.Presentation S (M i) (vars i) (rels i))
    (L : ∀ i, (Spec (.of (A i))).Modules)
    (a b : ∀ i, L i ≅ unitModule (Spec (.of (A i)))) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      frameUnitStage S M A e (fun i => affineCoframeUnit (A i) (a i) (b i)) R hSR :=
  exists_unit_stage S hS M A e vars rels Q
    (fun i => affineCoframeUnit (A i) (a i) (b i))

end FrobeniusSplitting
