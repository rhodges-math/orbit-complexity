import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AppendChart
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import Batteries.Tactic.Lint

/-! # The coefficient map of an append polynomial chart

The product chart and the projective-line isomorphism preserve the map to
the coefficient field. The polynomial chart therefore has its original
polynomial-algebra structure map.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory

namespace SchubertGeometry

private theorem inverse_over_base {C : Type*} [Category C] {B : C}
    {X Z A : Over B} {P : C} (E : X ≅ Z) (D : P ≅ Z.left)
    (I : X.left ≅ P) (hI : I = (Over.forget B).mapIso E ≪≫ D.symm)
    (π : Z ⟶ A) (b : P ⟶ A.left) (hb : D.hom ≫ π.left = b) :
    I.inv ≫ X.hom = b ≫ A.hom := by
  subst I
  change (D.hom ≫ E.inv.left) ≫ X.hom = b ≫ A.hom
  rw [Category.assoc, E.inv.w, ← π.w, ← Category.assoc, hb]

private theorem composite_over_base {C : Type*} [Category C] {B P : C}
    {X T : Over B} (f : X ⟶ T) (a : P ⟶ X.left) (b : P ⟶ B)
    (ha : a ≫ X.hom = b) :
    (a ≫ f.left) ≫ T.hom = b := by
  rw [Category.assoc, f.w]
  exact ha

private theorem polynomial_base {K A : Type u}
    [CommRing K] [CommRing A] [Algebra K A] :
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))) := by
  rw [← Spec.map_comp]
  rfl

private theorem simpleBorel_base {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    (simpleBorelLineIso G i A).inv ≫
      (((algSpec (.of K)).obj (.op A)) ⊗
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).hom =
      projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        ((algSpec (.of K)).obj (.op A)).hom := by
  let E := tensorIso (Iso.refl ((algSpec (.of K)).obj (.op A))) (simpleSchubertIso G i)
  let D := projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  let π := fst ((algSpec (.of K)).obj (.op A))
    (Over.mk (projectiveToSpec K (ULift.{u} (Fin 2))))
  have hD : D.hom ≫ π.left = projectiveToSpec A (ULift.{u} (Fin 2)) := by
    exact projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap K A)
  exact inverse_over_base E D (simpleBorelLineIso G i A) rfl π
    (projectiveToSpec A (ULift.{u} (Fin 2))) hD

private theorem append_base {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    {V T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T) :
    projectiveAppendChart G i A p c ≫ T.hom =
      projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  exact composite_over_base
    ((p ⊗ₘ 𝟙 (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c)
    (simpleBorelLineIso G i A).inv _ (simpleBorel_base G i A)

/-- The polynomial append chart preserves its polynomial-algebra map to
the coefficient field. -/
theorem appendPolynomialChart_base {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    {V T : Over (Spec (.of K))}
    (p : (algSpec (.of K)).obj (.op A) ⟶ V)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶ T)
    (ε : ULift.{u} (Fin 2)) :
    (projectiveLinePolynomialChart A ε ≫ projectiveAppendChart G i A p c) ≫ T.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))) := by
  calc
    _ = projectiveLinePolynomialChart A ε ≫
        (projectiveToSpec A (ULift.{u} (Fin 2)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
      (Category.assoc _ _ _).trans
        (congrArg (projectiveLinePolynomialChart A ε ≫ ·) (append_base G i A p c))
    _ = (projectiveLinePolynomialChart A ε ≫ projectiveToSpec A (ULift.{u} (Fin 2))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
      congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (projectiveLinePolynomialChart_base A ε)
    _ = _ := polynomial_base

end SchubertGeometry
