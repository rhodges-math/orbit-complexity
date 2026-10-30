import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import Mathlib.RingTheory.Smooth.Basic
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Append charts through two coefficient extensions

The two tensor cancellations identify the whole polynomial coefficient map.
The prescribed model projections then determine the same Cartesian chart.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

open private tensor_coordinate_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas

variable {S T R K A B : Type u}
variable [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
variable [Algebra S T] [Algebra T R] [Algebra S K] [Algebra T K] [Algebra R K]
variable [IsScalarTower S T K] [IsScalarTower T R K] [Algebra S A] [Algebra K B]

/-- Tensor cancellation identifies coefficients after the two intermediate extensions. -/
def iteratedAppendEquiv (e : K ⊗[S] A ≃ₐ[K] B) :
    K ⊗[R] (R ⊗[T] (T ⊗[S] A)) ≃ₐ[K] B :=
  (Algebra.TensorProduct.cancelBaseChange T R K K (T ⊗[S] A)).trans
    ((Algebra.TensorProduct.cancelBaseChange S T K K A).trans e)

private def finalCoefficient (e : K ⊗[S] A ≃ₐ[K] B) :
    R ⊗[T] (T ⊗[S] A) →+* B :=
  (iteratedAppendEquiv (T := T) (R := R) e).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom

private def oldCoefficient : A →+* R ⊗[T] (T ⊗[S] A) :=
  (Algebra.TensorProduct.includeRight :
      T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom

private def initialCoefficient (e : K ⊗[S] A ≃ₐ[K] B) : A →+* B :=
  e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

private theorem coefficient_composition (e : K ⊗[S] A ≃ₐ[K] B) :
    (finalCoefficient (T := T) (R := R) e).comp
      (oldCoefficient (S := S) (T := T) (R := R) (A := A)) =
        initialCoefficient e := by
  let eT : K ⊗[T] (T ⊗[S] A) ≃ₐ[K] B :=
    (Algebra.TensorProduct.cancelBaseChange S T K K A).trans e
  let phi : T ⊗[S] A →+* B :=
    eT.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have hR : (finalCoefficient (T := T) (R := R) e).comp
      (Algebra.TensorProduct.includeRight :
        T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom = phi :=
    tensor_coordinate_factor (S := T) (R := R) eT
  have hT : phi.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom =
      initialCoefficient e :=
    tensor_coordinate_factor (S := S) (R := T) e
  change (finalCoefficient (T := T) (R := R) e).comp
    ((Algebra.TensorProduct.includeRight :
      T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom) = _
  rw [← RingHom.comp_assoc, hR]
  exact hT

private def polynomialSpecMap {D E : Type u} [CommRing D] [CommRing E]
    (f : D →+* E) :
    Spec (.of (Polynomial E)) ⟶ Spec (.of (Polynomial D)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))

private theorem polynomial_spec_comp {D E F : Type u}
    [CommRing D] [CommRing E] [CommRing F] (f : D →+* E) (g : E →+* F) :
    polynomialSpecMap g ≫ polynomialSpecMap f = polynomialSpecMap (g.comp f) := by
  unfold polynomialSpecMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Polynomial.mapRingHom_comp]

/-- The polynomial scalar map through both extensions equals the original coefficient map. -/
theorem iteratedAppend_polynomial (e : K ⊗[S] A ≃ₐ[K] B) :
    polynomialSpecMap (finalCoefficient (T := T) (R := R) e) ≫
      polynomialSpecMap (oldCoefficient (S := S) (T := T) (R := R) (A := A)) =
        polynomialSpecMap (initialCoefficient e) := by
  rw [polynomial_spec_comp, coefficient_composition]

/-- The prescribed append chart stays Cartesian through both coefficient extensions. -/
theorem iteratedAppend_field_chart (e : K ⊗[S] A ≃ₐ[K] B)
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (n : Z ⟶ Y) (m : Z ⟶ X)
    (base : X ⟶ Spec (.of S)) (baseR : Y ⟶ Spec (.of R))
    (baseK : Z ⟶ Spec (.of K))
    (hK : IsPullback n baseK baseR
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (h₀ : IsPullback m baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hm : n ≫ q = m)
    (j₀ : Spec (.of (Polynomial A)) ⟶ X)
    (jR : Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] A)))) ⟶ Y)
    (jK : Spec (.of (Polynomial B)) ⟶ Z)
    (hjR : jR ≫ q =
      polynomialSpecMap (oldCoefficient (S := S) (T := T) (R := R) (A := A)) ≫ j₀)
    (hjRb : jR ≫ baseR =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A))))))
    (hjK : jK ≫ m = polynomialSpecMap (initialCoefficient e) ≫ j₀)
    (hjKb : jK ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial B)))) :
    IsPullback (polynomialSpecMap (finalCoefficient (T := T) (R := R) e)) jK jR n ∧
      jK ≫ n = polynomialSpecMap (finalCoefficient (T := T) (R := R) e) ≫ jR := by
  obtain ⟨_, _, _, hP⟩ := exists_scalar_polynomial_square R K
    (R ⊗[T] (T ⊗[S] A)) B (iteratedAppendEquiv (T := T) (R := R) e)
  exact append_scalar_field_chart q n m base baseR baseK
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (Spec.map (CommRingCat.ofHom (algebraMap S K))) hK h₀ hm
    (polynomialSpecMap (oldCoefficient (S := S) (T := T) (R := R) (A := A)))
    (polynomialSpecMap (finalCoefficient (T := T) (R := R) e))
    (polynomialSpecMap (initialCoefficient e))
    (iteratedAppend_polynomial (T := T) (R := R) e)
    (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A))))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial B)))) hP
    j₀ jR jK hjR hjRb hjK hjKb

end SchubertGeometry


set_option autoImplicit false
set_option maxHeartbeats 200000

namespace SchubertGeometry

universe v w

private def polynomialSpecIso {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) : Spec (.of (Polynomial B)) ≅ Spec (.of (Polynomial A)) :=
  Scheme.Spec.mapIso (Polynomial.mapAlgEquiv e).toRingEquiv.toCommRingCatIso.op

private theorem polynomialSpecIso_hom {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    (polynomialSpecIso e).hom = polynomialSpecMap e.toRingHom := rfl

private theorem polynomialSpecIso_inv {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    (polynomialSpecIso e).inv = polynomialSpecMap e.symm.toRingHom := rfl

section
variable {S T R A : Type u}
variable [CommRing S] [CommRing T] [CommRing R] [CommRing A]
variable [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
variable [Algebra S A]

private theorem cancel_old_coefficient :
    (Algebra.TensorProduct.cancelBaseChange S T R R A).toRingHom.comp
      (oldCoefficient (S := S) (T := T) (R := R) (A := A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom := by
  apply RingHom.ext
  intro a
  simp [oldCoefficient, Algebra.TensorProduct.includeRight_apply]

private theorem cancel_inverse_coefficient :
    (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
      oldCoefficient (S := S) (T := T) (R := R) (A := A) := by
  apply RingHom.ext
  intro a
  simp [oldCoefficient, Algebra.TensorProduct.includeRight_apply]

private theorem cancel_base_coefficient :
    (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toRingHom.comp
      (algebraMap R (R ⊗[S] A)) =
      algebraMap R (R ⊗[T] (T ⊗[S] A)) := by
  exact (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toAlgHom.comp_algebraMap

private theorem cancel_polynomial_coefficient :
    polynomialSpecMap (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toRingHom ≫
      polynomialSpecMap
        (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
      polynomialSpecMap (oldCoefficient (S := S) (T := T) (R := R) (A := A)) := by
  rw [polynomial_spec_comp, cancel_inverse_coefficient]

private theorem cancel_polynomial_base :
    polynomialSpecMap (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toRingHom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[S] A)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A))))) := by
  unfold polynomialSpecMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (Polynomial.mapAlgHom (Algebra.TensorProduct.cancelBaseChange S T R R
        A).symm.toAlgHom).comp_algebraMap

end
section
variable {S T R K A B : Type u}
variable [CommRing S] [CommRing T] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
variable [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
variable [Algebra S K] [Algebra T K] [Algebra R K]
variable [IsScalarTower S T K] [IsScalarTower T R K] [IsScalarTower S R K]
variable [Algebra S A] [Algebra K B]

private theorem cancel_field_coefficient (e : K ⊗[S] A ≃ₐ[K] B) :
    finalCoefficient (T := T) (R := R) e =
      (((Algebra.TensorProduct.cancelBaseChange S R K K A).trans e).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R ⊗[S] A →ₐ[R]
          K ⊗[R] (R ⊗[S] A)).toRingHom).comp
            (Algebra.TensorProduct.cancelBaseChange S T R R A).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul r y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz
    | tmul t a =>
      simp [finalCoefficient, iteratedAppendEquiv,
        Algebra.TensorProduct.includeRight_apply, Algebra.smul_def,
        IsScalarTower.algebraMap_apply T R K, mul_comm]

private theorem cancel_polynomial_field (e : K ⊗[S] A ≃ₐ[K] B) :
    polynomialSpecMap
      (((Algebra.TensorProduct.cancelBaseChange S R K K A).trans e).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R ⊗[S] A →ₐ[R]
          K ⊗[R] (R ⊗[S] A)).toRingHom) ≫
      polynomialSpecMap (Algebra.TensorProduct.cancelBaseChange S T R R A).toRingHom =
        polynomialSpecMap (finalCoefficient (T := T) (R := R) e) := by
  rw [polynomial_spec_comp, ← cancel_field_coefficient]

end

private theorem fixedFibreDiagram_smooth {J : Type v} [jCat : Category.{w} J]
    {S T : Type u} [sComm : CommRing S] [tComm : CommRing T]
    [sTAlg : Algebra S T] (N : J ⥤ CommAlgCat.{u} S)
    (hN : ∀ j, Algebra.Smooth S (N.obj j)) :
    ∀ j, Algebra.Smooth T
      ((@fixedFibreDiagram.{u,v,w} J jCat S T T sComm tComm tComm sTAlg
        (@Algebra.id T (@CommRing.toCommSemiring T tComm)) sTAlg
        (@IsScalarTower.right S T (@CommRing.toCommSemiring S sComm)
          (@Ring.toSemiring T (@CommRing.toRing T tComm)) sTAlg) N).obj j) := by
  intro j
  exact @Algebra.Smooth.baseChange S sComm (N.obj j) T
    (@CommAlgCat.commRing S sComm (N.obj j))
    (@CommAlgCat.algebra S sComm (N.obj j)) tComm sTAlg (hN j)

private theorem fixedFibreDiagram_smooth_twice {J : Type v} [jCat : Category.{w} J]
    {S T R : Type u} [sComm : CommRing S] [tComm : CommRing T]
    [rComm : CommRing R] [sTAlg : Algebra S T] [tRAlg : Algebra T R]
    (N : J ⥤ CommAlgCat.{u} S) (hN : ∀ j, Algebra.Smooth S (N.obj j)) :
    ∀ j, Algebra.Smooth R
      ((@fixedFibreDiagram.{u,v,w} J jCat T R R tComm rComm rComm tRAlg
        (@Algebra.id R (@CommRing.toCommSemiring R rComm)) tRAlg
        (@IsScalarTower.right T R (@CommRing.toCommSemiring T tComm)
          (@Ring.toSemiring R (@CommRing.toRing R rComm)) tRAlg)
        (@fixedFibreDiagram.{u,v,w} J jCat S T T sComm tComm tComm sTAlg
          (@Algebra.id T (@CommRing.toCommSemiring T tComm)) sTAlg
          (@IsScalarTower.right S T (@CommRing.toCommSemiring S sComm)
            (@Ring.toSemiring T (@CommRing.toRing T tComm)) sTAlg) N)).obj j) := by
  exact @fixedFibreDiagram_smooth.{u,v,w} J jCat T R tComm rComm tRAlg
    (@fixedFibreDiagram.{u,v,w} J jCat S T T sComm tComm tComm sTAlg
      (@Algebra.id T (@CommRing.toCommSemiring T tComm)) sTAlg
      (@IsScalarTower.right S T (@CommRing.toCommSemiring S sComm)
        (@Ring.toSemiring T (@CommRing.toRing T tComm)) sTAlg) N)
    (@fixedFibreDiagram_smooth.{u,v,w} J jCat S T sComm tComm sTAlg N hN)


private theorem map_quadratic_relations {I : Type v} {A B C : I → Type u}
    [aComm : ∀ s, CommRing (A s)] [bComm : ∀ s, CommRing (B s)]
    [cComm : ∀ s, CommRing (C s)]
    (mu : ∀ s, A s →+* B s) (f : ∀ s, A s →+* C s) (g : ∀ s, B s →+* C s)
    (hcomp : ∀ s, (g s).comp (mu s) = f s)
    (P : ∀ s, Polynomial (A s)) (Q : ∀ s, Polynomial (C s)) (c : ∀ s, C s)
    (hP : ∀ s, (P s).natDegree ≤ 2 ∧ Polynomial.map (f s) (P s) = Q s ∧
      f s ((P s).coeff 2) = c s ∧
      ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n) :
    ∀ s, (Polynomial.map (mu s) (P s)).natDegree ≤ 2 ∧
      Polynomial.map (g s) (Polynomial.map (mu s) (P s)) = Q s ∧
      g s ((Polynomial.map (mu s) (P s)).coeff 2) = c s ∧
      ∀ n : ℕ, (Polynomial.map (mu s) (P s) ^ n).coeff (2 * n) =
        ((Polynomial.map (mu s) (P s)).coeff 2) ^ n := by
  intro s
  refine ⟨Polynomial.natDegree_map_le.trans (hP s).1, ?_, ?_, ?_⟩
  · rw [Polynomial.map_map, hcomp]
    exact (hP s).2.1
  · rw [Polynomial.coeff_map, ← RingHom.comp_apply, hcomp]
    exact (hP s).2.2.1
  · intro n
    rw [← Polynomial.map_pow, Polynomial.coeff_map, (hP s).2.2.2 n, map_pow,
      Polynomial.coeff_map]


private theorem scalar_comparison_value {K : Type u} [kField : Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R) {J : Type u} [jCat : Category.{u} J]
    (N : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    ∀ (v : (fixedFibreDiagram (R := R) (M := R) N) ⋙
        forget₂ (CommAlgCat R) CommRingCat ⟶ F ⋙ forget₂ (CommAlgCat K) CommRingCat),
      (∀ s x, (v.app s).hom x = e s
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (N.obj s)) x)) →
      ∀ s x, (@scalarDiagramComparison.{u,u,u} K kField S R hSR J jCat N F e s)
        ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  intro v hv s x
  rw [hv]
  induction x using TensorProduct.inductionOn with
  | tmul t a =>
    rw [@scalarDiagramComparison_tmul.{u,u,u} K kField S R hSR J jCat N F e s 1 t a,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mul_one]
    rfl
  | add x y hx hy =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

private theorem coordinate_comparison {K : Type u} [kField : Field K]
    (S T R : Subalgebra ℤ K) (hST : S ≤ T) (hTR : T ≤ R)
    {J : Type u} [jCat : Category.{u} J]
    (M₀ : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e₀ : ∀ s, K ⊗[S] M₀.obj s ≃ₐ[K] F.obj s)
    (he₀ : ∀ s t (f : s ⟶ t), (e₀ t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (M₀.map f).hom) =
        (F.map f).hom.comp (e₀ s).toAlgHom) :
    letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    letI : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
    letI : IsScalarTower S T K :=
      Subalgebra.inclusion.isScalarTower_right hST K
    letI : IsScalarTower T R K :=
      Subalgebra.inclusion.isScalarTower_right hTR K
    let MT := @fixedFibreDiagram.{u,u,u} J jCat S T T
      inferInstance inferInstance inferInstance inferInstance
      (Algebra.id T) inferInstance (@IsScalarTower.right S T inferInstance inferInstance
          inferInstance) M₀
    let eT := @scalarDiagramComparison.{u,u,u} K kField S T hST J jCat M₀ F e₀
    let NR := @fixedFibreDiagram.{u,u,u} J jCat T R R
      inferInstance inferInstance inferInstance inferInstance
      (Algebra.id R) inferInstance (@IsScalarTower.right T R inferInstance inferInstance
          inferInstance) MT
    ∀ (N : J ⥤ CommAlgCat.{u} R) (hN : N = NR)
      (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat),
      (∀ s x, eT s
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (MT.obj s)) (((eqToHom hN).app s).hom x)) =
          (v.app s).hom x) →
      ∃ e₂ : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s,
        HEq e₂ (@scalarDiagramComparison.{u,u,u} K kField T R hTR J jCat MT F eT) ∧
        (∀ s t (f : s ⟶ t), (e₂ t).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
            (F.map f).hom.comp (e₂ s).toAlgHom) ∧
        ∀ s x, e₂ s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x := by
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower S T K :=
    Subalgebra.inclusion.isScalarTower_right hST K
  let : IsScalarTower T R K :=
    Subalgebra.inclusion.isScalarTower_right hTR K
  let MT := @fixedFibreDiagram.{u,u,u} J jCat S T T
    inferInstance inferInstance inferInstance inferInstance
    (Algebra.id T) inferInstance (@IsScalarTower.right S T inferInstance inferInstance
        inferInstance) M₀
  let eT := @scalarDiagramComparison.{u,u,u} K kField S T hST J jCat M₀ F e₀
  let NR := @fixedFibreDiagram.{u,u,u} J jCat T R R
    inferInstance inferInstance inferInstance inferInstance
    (Algebra.id R) inferInstance (@IsScalarTower.right T R inferInstance inferInstance
        inferInstance) MT
  change ∀ (N : J ⥤ CommAlgCat.{u} R) (hN : N = NR) (v : _), _
  intro N hN v hev
  cases hN
  let e₂ := @scalarDiagramComparison.{u,u,u} K kField T R hTR J jCat MT F eT
  have heT := @scalarDiagramComparison_natural.{u,u,u}
    K kField S T hST J jCat M₀ F e₀ he₀
  have he₂ := @scalarDiagramComparison_natural.{u,u,u}
    K kField T R hTR J jCat MT F eT heT
  have hvalue := @scalar_comparison_value.{u}
    K kField T R hTR J jCat MT F eT v
      (fun s x => (hev s x).symm)
  exact ⟨e₂, HEq.rfl, he₂, hvalue⟩

namespace RetainedCharacter

private theorem join_chart_squares {C : Type u} [Category C]
    {U V X Y Z A B P Q : C} {f : U ⟶ X} {q : X ⟶ Y} {r : Y ⟶ Z}
    (E₀ : V ≅ A) (E₁ : U ≅ B) (Ecan : B ≅ Q) (Eflat : U ≅ Q)
    {v : V ⟶ Y} {k₁ : B ⟶ A} {k₀ : A ⟶ P} {leg : P ⟶ Z}
    {k : Q ⟶ P}
    (hE : Eflat = E₁ ≪≫ Ecan)
    (hs : f ≫ q = E₁.hom ≫ k₁ ≫ E₀.inv ≫ v)
    (h₀ : v ≫ r = E₀.hom ≫ k₀ ≫ leg)
    (hc : Ecan.hom ≫ k = k₁ ≫ k₀) :
    f ≫ (q ≫ r) = Eflat.hom ≫ k ≫ leg := by
  subst Eflat
  change f ≫ (q ≫ r) = (E₁.hom ≫ Ecan.hom) ≫ k ≫ leg
  calc
    f ≫ (q ≫ r) = E₁.hom ≫ k₁ ≫ E₀.inv ≫ (v ≫ r) := by
      rw [← Category.assoc, hs]
      simp only [Category.assoc]
    _ = E₁.hom ≫ k₁ ≫ E₀.inv ≫ (E₀.hom ≫ k₀ ≫ leg) :=
      congrArg (fun z => E₁.hom ≫ k₁ ≫ E₀.inv ≫ z) h₀
    _ = E₁.hom ≫ (k₁ ≫ k₀) ≫ leg := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (E₁.hom ≫ Ecan.hom) ≫ k ≫ leg := by
      simpa only [Category.assoc] using
        congrArg (fun z => E₁.hom ≫ z ≫ leg) hc.symm

private theorem join_chart_base {C : Type u} [Category C]
    {U X Y A B : C} (E : U ≅ A) (Ecan : A ≅ B) (Eflat : U ≅ B)
    {f : U ⟶ X} {baseX : X ⟶ Y} {baseA : A ⟶ Y} {baseB : B ⟶ Y}
    (hE : Eflat = E ≪≫ Ecan)
    (hb : f ≫ baseX = E.hom ≫ baseA) (hc : Ecan.hom ≫ baseB = baseA) :
    f ≫ baseX = Eflat.hom ≫ baseB := by
  subst Eflat
  change f ≫ baseX = (E.hom ≫ Ecan.hom) ≫ baseB
  rw [Category.assoc, hc]
  exact hb

private theorem cancel_polynomial_pair {S T R A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R]
    [Algebra S A] :
    polynomialSpecMap (Algebra.TensorProduct.cancelBaseChange S T R R A).symm.toRingHom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
    polynomialSpecMap (Algebra.TensorProduct.includeRight :
      T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  exact (cancel_polynomial_coefficient (S := S) (T := T) (R := R) (A := A)).trans
    (polynomial_spec_comp
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom
      (Algebra.TensorProduct.includeRight :
        T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom).symm

private def cancel_chart_iso {S T R A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R] [Algebra S A] :
    Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] A)))) ≅ Spec (.of (Polynomial (R ⊗[S] A))) :=
  (polynomialSpecIso (Algebra.TensorProduct.cancelBaseChange S T R R A)).symm

private theorem cancel_chart_pair {S T R A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R] [Algebra S A] :
    (cancel_chart_iso (S := S) (T := T) (R := R) (A := A)).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
    polynomialSpecMap (Algebra.TensorProduct.includeRight :
      T ⊗[S] A →ₐ[T] R ⊗[T] (T ⊗[S] A)).toRingHom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  change (polynomialSpecIso (Algebra.TensorProduct.cancelBaseChange S T R R A)).inv ≫ _ = _
  rw [polynomialSpecIso_inv]
  exact cancel_polynomial_pair

private theorem cancel_chart_base {S T R A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing A]
    [Algebra S T] [Algebra S R] [Algebra T R] [IsScalarTower S T R] [Algebra S A] :
    (cancel_chart_iso (S := S) (T := T) (R := R) (A := A)).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[S] A)))) =
    Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] A))))) := by
  change (polynomialSpecIso (Algebra.TensorProduct.cancelBaseChange S T R R A)).inv ≫ _ = _
  rw [polynomialSpecIso_inv]
  exact cancel_polynomial_base

private theorem spec_square {A B C D : CommRingCat.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (he : f ≫ g = h ≫ k) :
    Spec.map g ≫ Spec.map f = Spec.map k ≫ Spec.map h := by
  rw [← Spec.map_comp, ← Spec.map_comp, he]

private theorem evaluation_base {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) :
    (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).comp
      (algebraMap R A) = (algebraMap K B).comp (algebraMap R K) := by
  let : Algebra R B := ((algebraMap K B).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ((e.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)).comp_algebraMap

private theorem projection_evaluation {R K : Type u}
    [rComm : CommRing R] [kComm : CommRing K] [rKAlg : Algebra R K]
    {I : Type v} [iCategory : Category.{w} I]
    (N : I ⥤ CommAlgCat.{u} R) (F : I ⥤ CommAlgCat.{u} K)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (E : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (hE : ∀ s x, E s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x)
    (cN : Cocone (N.op ⋙ algSpec (.of R)))
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ cN.pt.left)
    (hq : q = @scalarModelProjection.{u,v,w} R K rComm kComm I iCategory
      N F v cN cF hcF) :
    ∀ s, (cF.ι.app (Opposite.op s)).left ≫ q =
      Spec.map (CommRingCat.ofHom
        ((E s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cN.ι.app (Opposite.op s)).left := by
  intro s
  have hmap : CommRingCat.ofHom
      ((E s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = v.app s :=
    CommRingCat.hom_ext (RingHom.ext (hE s))
  exact ((congrArg (fun f => (cF.ι.app (Opposite.op s)).left ≫ f) hq).trans
    (@scalarModelProjection_node.{u,v,w} R K rComm kComm I iCategory
      N F v cN cF hcF s).symm).trans
    (congrArg (fun f => Spec.map f ≫ (cN.ι.app (Opposite.op s)).left) hmap.symm)

private theorem scalar_factor {K : Type u} [Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R) {J : Type u} [Category.{u} J]
    (N : J ⥤ CommAlgCat.{u} S) (F : J ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s) :
    let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    ∀ s,
      ((scalarDiagramComparison S R hSR N F e s).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom).comp
          (Algebra.TensorProduct.includeRight : N.obj s →ₐ[S] R ⊗[S] N.obj s).toRingHom =
        (e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
  dsimp only
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  intro s
  apply RingHom.ext
  intro x
  change scalarDiagramComparison S R hSR N F e s
    ((1 : K) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x)) = e s ((1 : K) ⊗ₜ[S] x)
  rw [scalarDiagramComparison_tmul]
  simp only [map_one, one_mul]

private theorem node_base_square {C : Type u} [Category C]
    {A B X Y S T : C}
    (b : A ⟶ Y) (m : Y ⟶ X) (v : A ⟶ B) (leg : B ⟶ X)
    (baseY : Y ⟶ S) (baseX : X ⟶ T) (a : S ⟶ T)
    (u : A ⟶ S) (baseB : B ⟶ T)
    (hb : b ≫ baseY = u) (hm : m ≫ baseX = baseY ≫ a)
    (hl : leg ≫ baseX = baseB) (hv : v ≫ baseB = u ≫ a) :
    (b ≫ m) ≫ baseX = (v ≫ leg) ≫ baseX := by
  calc
    (b ≫ m) ≫ baseX = b ≫ (baseY ≫ a) := by rw [Category.assoc, hm]
    _ = u ≫ a := by rw [← Category.assoc, hb]
    _ = v ≫ baseB := hv.symm
    _ = (v ≫ leg) ≫ baseX := by rw [Category.assoc, hl]

private theorem boundary_square {C : Type u} [Category C]
    {A X B Y Z : C} (i : A ⟶ X) (n : A ⟶ B) (m : X ⟶ Y) (r : B ⟶ Y)
    (h : IsPullback i n m r) (q : Z ⟶ Y) [HasPullback q r]
    (m' : X ⟶ Z) (hm : m' ≫ q = m) (n' : A ⟶ pullback q r)
    (hf : n' ≫ pullback.fst q r = i ≫ m')
    (hs : n' ≫ pullback.snd q r = n) :
    IsPullback i n' m' (pullback.fst q r) := by
  have houter : IsPullback i (n' ≫ pullback.snd q r) (m' ≫ q) r := by
    simpa only [hs, hm] using h
  exact houter.of_bot hf.symm (IsPullback.of_hasPullback q r)

private theorem chart_factor_transport
    {C : Type u} [Category.{v} C] {X V N F : C}
    (E : V ≅ N) (Ecan : N ≅ F)
    (π : X ⟶ V) (m : X ⟶ N) (mFlat : X ⟶ F)
    (hπ : π = m ≫ E.inv) (hm : mFlat ≫ Ecan.inv = m) :
    π = mFlat ≫ (E ≪≫ Ecan).inv := by
  calc
    π = m ≫ E.inv := hπ
    _ = (mFlat ≫ Ecan.inv) ≫ E.inv :=
      congrArg (fun z => z ≫ E.inv) hm.symm
    _ = mFlat ≫ (E ≪≫ Ecan).inv := Category.assoc _ _ _

section Coefficients

variable {S₀ S R K A B : Type u}
    [CommRing S₀] [CommRing S] [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra S₀ S] [Algebra S R] [Algebra S₀ R] [IsScalarTower S₀ S R]
    [Algebra S₀ K] [Algebra S K] [Algebra R K]
    [IsScalarTower S₀ S K] [IsScalarTower S R K] [IsScalarTower S₀ R K]
    [Algebra S₀ A] [Algebra K B]

private theorem scalar_initial_coefficient
    (e : K ⊗[S₀] A ≃ₐ[K] B)
    (eR : K ⊗[R] (R ⊗[S₀] A) ≃ₐ[K] B)
    (heR : ∀ (k : K) (r : R) (a : A),
      eR (k ⊗ₜ[R] (r ⊗ₜ[S₀] a)) =
        e ((algebraMap R K r * k) ⊗ₜ[S₀] a)) :
    initialCoefficient (S := R) eR =
      ((Algebra.TensorProduct.cancelBaseChange S₀ R K K A).trans e).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          R ⊗[S₀] A →ₐ[R] K ⊗[R] (R ⊗[S₀] A)).toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul r a =>
      change eR (1 ⊗ₜ[R] (r ⊗ₜ[S₀] a)) =
        e ((Algebra.TensorProduct.cancelBaseChange S₀ R K K A)
          (1 ⊗ₜ[R] (r ⊗ₜ[S₀] a)))
      simpa only [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def] using
        heR 1 r a

private theorem scalar_polynomial_field
    (e : K ⊗[S₀] A ≃ₐ[K] B)
    (eR : K ⊗[R] (R ⊗[S₀] A) ≃ₐ[K] B)
    (heR : ∀ (k : K) (r : R) (a : A),
      eR (k ⊗ₜ[R] (r ⊗ₜ[S₀] a)) =
        e ((algebraMap R K r * k) ⊗ₜ[S₀] a)) :
    polynomialSpecMap (initialCoefficient (S := R) eR) ≫
        (cancel_chart_iso (S := S₀) (T := S) (R := R) (A := A)).inv =
      polynomialSpecMap (finalCoefficient (T := S) (R := R) e) := by
  change polynomialSpecMap (initialCoefficient (S := R) eR) ≫
      (polynomialSpecIso (Algebra.TensorProduct.cancelBaseChange S₀ S R R A)).hom = _
  rw [polynomialSpecIso_hom, scalar_initial_coefficient e eR heR]
  exact cancel_polynomial_field (T := S) (R := R) e

private theorem scalar_field_chart_equation
    (e : K ⊗[S₀] A ≃ₐ[K] B)
    (eR : K ⊗[R] (R ⊗[S₀] A) ≃ₐ[K] B)
    (heR : ∀ (k : K) (r : R) (a : A),
      eR (k ⊗ₜ[R] (r ⊗ₜ[S₀] a)) =
        e ((algebraMap R K r * k) ⊗ₜ[S₀] a))
    {V : Scheme.{u}}
    (E : V ≅ Spec (.of (Polynomial (R ⊗[S] (S ⊗[S₀] A)))))
    (π : Spec (.of (Polynomial B)) ⟶ V)
    (hπ : π = polynomialSpecMap (finalCoefficient (T := S) (R := R) e) ≫ E.inv) :
    π = polynomialSpecMap (initialCoefficient (S := R) eR) ≫
      (E ≪≫ cancel_chart_iso (S := S₀) (T := S) (R := R) (A := A)).inv := by
  exact @chart_factor_transport.{u+1,u} Scheme.{u} Scheme.instCategory
    (Spec (.of (Polynomial B))) V
    (Spec (.of (Polynomial (R ⊗[S] (S ⊗[S₀] A)))))
    (Spec (.of (Polynomial (R ⊗[S₀] A))))
    E (cancel_chart_iso (S := S₀) (T := S) (R := R) (A := A)) π
    (polynomialSpecMap (finalCoefficient (T := S) (R := R) e))
    (polynomialSpecMap (initialCoefficient (S := R) eR)) hπ
    (scalar_polynomial_field (S := S) e eR heR)

end Coefficients

end RetainedCharacter


end SchubertGeometry
