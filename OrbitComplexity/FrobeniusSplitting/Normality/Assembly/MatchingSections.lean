import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeCoefficients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Sections of character matching modules from coefficient equations

An exponent-one coefficient cochain gives sections for every power of the
character. The same coefficient sections respect scalar morphisms between the
coefficient rings.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.CharacterLine

noncomputable section

universe u

namespace FrobeniusSplitting.RetainedCharacter

open private singletonIndex singletonArrow localFunctions coefficientSection
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

private theorem spec_coefficient_map {A B : CommRingCat.{u}} (f : A ⟶ B) (x : A) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) =
      (Scheme.ΓSpecIso B).inv (f.hom x) :=
  (congrArg (fun q : A ⟶ Γ(Spec B, ⊤) => q x)
    (Scheme.ΓSpecIso_inv_naturality f)).symm

private theorem coefficient_section_equation {A B C : CommRingCat.{u}}
    (f : A ⟶ C) (g : B ⟶ C) (x : A) (y : B) (d : C)
    (h : f.hom x = g.hom y * d) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) =
      (Spec.map g).appTop ((Scheme.ΓSpecIso B).inv y) * (Scheme.ΓSpecIso C).inv d := by
  rw [spec_coefficient_map, spec_coefficient_map]
  exact (congrArg (fun z : C => (Scheme.ΓSpecIso C).inv z) h).trans
    (map_mul (Scheme.ΓSpecIso C).inv.hom _ _)

private theorem relative_coefficients_match {S : Scheme.{u}}
    {X Y Q : Over S} (f : Q ⟶ X) (g : Q ⟶ Y)
    (x : Γ(X.left, ⊤)) (y : Γ(Y.left, ⊤)) (d : Γ(Q.left, ⊤))
    (h : f.left.appTop x = g.left.appTop y * d) :
    relativeCoefficient S X x ≫ relativeFunctionsMap S f =
      relativeCoefficient S Y y ≫ relativeFunctionsMap S g ≫ relativeFunctionsSmul S Q d := by
  exact (relativeCoefficient_pullback S f x).trans
    ((congrArg (relativeCoefficient S Q) h).trans
      ((relativeCoefficient_multiply S Q (g.left.appTop y) d).symm.trans
        ((congrArg (fun t => t ≫ relativeFunctionsSmul S Q d)
          (relativeCoefficient_pullback S g y).symm).trans
            (Category.assoc _ _ _))))

private theorem coefficient_naturality {J : Type u}
    (N F : {s : Finset J // s.Nonempty} ⥤ CommRingCat.{u}) (v : N ⟶ F)
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) (x : N.obj s) :
    (v.app t).hom ((N.map f).hom x) = (F.map f).hom ((v.app s).hom x) :=
  congrArg (fun q : N.obj s ⟶ F.obj t => q.hom x)
    (v.naturality f)

/-- Scalar comparison of an affine coefficient section, for every exponent. -/
theorem coefficientSection_scalar {A B : CommRingCat.{u}}
    (f : A ⟶ B) (x : A) (n : ℕ) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv (x ^ n)) =
      (Scheme.ΓSpecIso B).inv ((f.hom x) ^ n) :=
  (spec_coefficient_map f (x ^ n)).trans
    (congrArg (fun z : B => (Scheme.ΓSpecIso B).inv z) (map_pow f.hom x n))

/-- Injective comparisons of coefficient diagrams descend the exponent-one
matching equations, using only naturality and the scalar ring equations. -/
theorem coefficient_cochain_descends {J : Type u}
    (N F : {s : Finset J // s.Nonempty} ⥤ CommRingCat.{u}) (v : N ⟶ F)
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (r : ∀ j : J, N.obj (singletonIndex j))
    (h : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (F.map (singletonArrow s j hj)).hom ((v.app (singletonIndex j)).hom (r j)) =
        (F.map (singletonArrow s k hk)).hom ((v.app (singletonIndex k)).hom (r k)) *
          (v.app s).hom (delta s j hj k hk : N.obj s)) :
    ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (r j) =
        (N.map (singletonArrow s k hk)).hom (r k) * (delta s j hj k hk : N.obj s) := by
  intro s j hj k hk
  apply hv s
  rw [map_mul, coefficient_naturality, coefficient_naturality]
  exact h s j hj k hk

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (r : ∀ j : J, N.obj (singletonIndex j))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (r j) =
        (N.map (singletonArrow s k hk)).hom (r k) * (delta s j hj k hk : N.obj s))

/-- A chart coefficient as a section of its relative function module. -/
def ringCoefficientSection (j : J) (x : N.obj (singletonIndex j)) :
    SheafOfModules.unit cG.pt.left.ringCatSheaf ⟶ localFunctions N cG j :=
  relativeCoefficient cG.pt.left (node N cG (singletonIndex j))
    (coefficientSection N cG (singletonIndex j) x)

include hr in
private theorem coefficient_power_equation (n : ℕ)
    (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val) :
    (N.map (singletonArrow s j hj)).hom ((r j) ^ n) =
      (N.map (singletonArrow s k hk)).hom ((r k) ^ n) *
        (delta s j hj k hk : N.obj s) ^ n := by
  rw [map_pow, map_pow, hr s j hj k hk, mul_pow]

include hr in
private theorem coefficient_sections_match (n : ℕ)
    (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val) :
    ringCoefficientSection N cG j ((r j) ^ n) ≫
        relativeFunctionsMap cG.pt.left (nodeMap N cG (singletonArrow s j hj)) =
      ringCoefficientSection N cG k ((r k) ^ n) ≫
        relativeFunctionsMap cG.pt.left (nodeMap N cG (singletonArrow s k hk)) ≫
          relativeFunctionsSmul cG.pt.left (node N cG s)
            (coefficientSection N cG s ((delta s j hj k hk : N.obj s) ^ n)) := by
  apply relative_coefficients_match
  exact coefficient_section_equation
    (CommRingCat.ofHom (N.map (singletonArrow s j hj)).hom.toRingHom)
    (CommRingCat.ofHom (N.map (singletonArrow s k hk)).hom.toRingHom)
    ((r j) ^ n) ((r k) ^ n) ((delta s j hj k hk : N.obj s) ^ n)
    (coefficient_power_equation N delta r hr n s j hj k hk)

/-- The coefficient cochain defines a global section of every character power's
matching module, without making another choice of line or coefficients. -/
def coefficientMatchingSection (n : ℕ) :
    SheafOfModules.unit cG.pt.left.ringCatSheaf ⟶ matchingModule N cG delta n :=
  lift N cG delta n (fun j => ringCoefficientSection N cG j ((r j) ^ n))
    (coefficient_sections_match N cG delta r hr n)

/-- The global coefficient section has the prescribed power as every chart coordinate. -/
theorem coefficientMatchingSection_coordinate (n : ℕ) (j : J) :
    coefficientMatchingSection N cG delta r hr n ≫ coordinate N cG delta n j =
      ringCoefficientSection N cG j ((r j) ^ n) :=
  lift_coordinate N cG delta n (fun j => ringCoefficientSection N cG j ((r j) ^ n))
    (coefficient_sections_match N cG delta r hr n) j

/-- A section having these coefficient coordinates is the same global matching section. -/
theorem coefficientMatchingSection_unique (n : ℕ)
    (s : SheafOfModules.unit cG.pt.left.ringCatSheaf ⟶ matchingModule N cG delta n)
    (hs : ∀ j : J, s ≫ coordinate N cG delta n j =
      ringCoefficientSection N cG j ((r j) ^ n)) :
    s = coefficientMatchingSection N cG delta r hr n :=
  coordinate_hom_ext N cG delta n _ _ (fun j => (hs j).trans
    (coefficientMatchingSection_coordinate N cG delta r hr n j).symm)

end FrobeniusSplitting.RetainedCharacter
