import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingSections
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeCoefficients
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Coefficients of matching sections and coefficient extensions

Relative coefficient sections reflect equality of their coefficients. Thus a
matching identity of sections gives the corresponding ring equation.
Natural coefficient maps also carry unit cocycles to the same enlarged diagram.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u v w

namespace FrobeniusSplitting.CharacterLine

private theorem relativeCoefficient_one {S : Scheme.{u}} (X : Over S)
    (r : Γ(X.left, ⊤)) :
    ((relativeCoefficient S X r).val.app (op ⊤)).hom (1 : Γ(S, ⊤)) = r := by
  rw [relativeCoefficient_app]
  simp only [map_one, mul_one]
  change (X.left.presheaf.map (𝟙 (op ⊤))).hom r = r
  rw [X.left.presheaf.map_id]
  rfl

/-- Equality of relative coefficient sections reflects equality of their
original global coefficients. -/
theorem relativeCoefficient_injective {S : Scheme.{u}} (X : Over S) :
    Function.Injective (relativeCoefficient S X) := by
  intro r s h
  have he := congrArg
    (fun f : SheafOfModules.unit S.ringCatSheaf ⟶ relativeFunctionsObj S X =>
      ((f.val.app (op ⊤)).hom) (1 : Γ(S, ⊤))) h
  exact (relativeCoefficient_one X r).symm.trans
    (he.trans (relativeCoefficient_one X s))

/-- A matching equation of relative coefficient sections gives the matching
identity of global regular functions. -/
theorem coefficient_matching_reflects {S : Scheme.{u}} {X Y Q : Over S}
    (f : Q ⟶ X) (g : Q ⟶ Y)
    (r : Γ(X.left, ⊤)) (s : Γ(Y.left, ⊤)) (d : Γ(Q.left, ⊤))
    (h : relativeCoefficient S X r ≫ relativeFunctionsMap S f =
      relativeCoefficient S Y s ≫ relativeFunctionsMap S g ≫ relativeFunctionsSmul S Q d) :
    f.left.appTop r = g.left.appTop s * d := by
  apply relativeCoefficient_injective Q
  exact (relativeCoefficient_pullback S f r).symm.trans
    (h.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ relativeFunctionsSmul S Q d)
        (relativeCoefficient_pullback S g s)).trans
          (relativeCoefficient_multiply S Q (g.left.appTop s) d))))

end FrobeniusSplitting.CharacterLine

namespace FrobeniusSplitting.RetainedCharacter

open private spec_coefficient_map
  from OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingSections

/-- A matching identity of affine global functions reflects the ring equation
under the canonical affine global-section isomorphisms. -/
theorem affine_coefficient_reflects {A B C : CommRingCat.{u}}
    (f : A ⟶ C) (g : B ⟶ C) (x : A) (y : B) (d : C)
    (h : (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) =
      (Spec.map g).appTop ((Scheme.ΓSpecIso B).inv y) * (Scheme.ΓSpecIso C).inv d) :
    f.hom x = g.hom y * d := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso C).inv).injective
  calc
    (Scheme.ΓSpecIso C).inv (f.hom x) =
        (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) :=
      (spec_coefficient_map f x).symm
    _ = (Spec.map g).appTop ((Scheme.ΓSpecIso B).inv y) *
        (Scheme.ΓSpecIso C).inv d := h
    _ = (Scheme.ΓSpecIso C).inv (g.hom y) * (Scheme.ΓSpecIso C).inv d :=
      congrArg (fun z => z * (Scheme.ΓSpecIso C).inv d) (spec_coefficient_map g y)
    _ = (Scheme.ΓSpecIso C).inv (g.hom y * d) :=
      (map_mul (Scheme.ΓSpecIso C).inv.hom _ _).symm

/-- Pulling back an affine coefficient through an arbitrary affine scheme
morphism agrees with its ring preimage, for every power. -/
theorem affine_preimage_coefficient {A B : CommRingCat.{u}}
    (f : Spec B ⟶ Spec A) (x : A) (n : ℕ) :
    f.appTop ((Scheme.ΓSpecIso A).inv (x ^ n)) =
      (Scheme.ΓSpecIso B).inv (((Spec.preimage f).hom x) ^ n) := by
  simpa only [Spec.map_preimage] using
    coefficientSection_scalar (Spec.preimage f) x n

/-- The canonical right tensor inclusion is natural on the fixed coefficient
diagram. -/
def scalarCoefficientMap {I : Type v} [Category.{w} I]
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (N : I ⥤ CommAlgCat.{u} R) :
    N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      fixedFibreDiagram (R := T) (M := T) N ⋙ forget₂ (CommAlgCat T) CommRingCat where
  app s := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  naturality {s t} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (1 : T) ⊗ₜ[R] ((N.map f).hom x) =
      Algebra.TensorProduct.map (AlgHom.id T T) (N.map f).hom ((1 : T) ⊗ₜ[R] x)
    simp only [Algebra.TensorProduct.map_tmul, map_one]

/-- Evaluation after coefficient enlargement agrees with the original
evaluation on the canonical right tensor inclusion. -/
theorem scalarEvaluation_compatible {R T K A B : Type u}
    [CommRing R] [CommRing T] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra T K] [Algebra R K] [IsScalarTower R T K]
    [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) (f : A →+* B) (g : T ⊗[R] A →+* B)
    (hf : ∀ x, e ((1 : K) ⊗ₜ[R] x) = f x)
    (hg : ∀ x, g x = e (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R T K) (AlgHom.id R A) x)) (x : A) :
    g ((1 : T) ⊗ₜ[R] x) = f x := by
  rw [hg, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  exact hf x

variable {J : Type u}
    (N F : {s : Finset J // s.Nonempty} ⥤ CommRingCat.{u}) (v : N ⟶ F)

/-- The same transition unit, carried by a natural coefficient morphism. -/
def unitCoefficientImage
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) : (F.obj s)ˣ :=
  Units.map (v.app s).hom.toMonoidHom (delta s j hj k hk)

/-- Carrying transition units by a coefficient morphism preserves their
cocycle identity. -/
theorem unitCoefficientImage_cocycle
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk) :
    ∀ s j hj k hk l hl,
      unitCoefficientImage N F v delta s j hj l hl =
        unitCoefficientImage N F v delta s k hk l hl *
          unitCoefficientImage N F v delta s j hj k hk := by
  intro s j hj k hk l hl
  exact (congrArg (Units.map (v.app s).hom.toMonoidHom)
    (hco s j hj k hk l hl)).trans
      (map_mul (Units.map (v.app s).hom.toMonoidHom) _ _)

/-- Carrying transition units by a natural coefficient morphism preserves
their restriction equations. -/
theorem unitCoefficientImage_natural
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom
          (unitCoefficientImage N F v delta s j hj k hk) =
        unitCoefficientImage N F v delta t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
  intro s t f j hj k hk
  apply Units.ext
  have hv := congrArg
    (fun g : N.obj s ⟶ F.obj t => g.hom (delta s j hj k hk : N.obj s))
      (v.naturality f)
  have hd := congrArg (fun z : (N.obj t)ˣ => (z : N.obj t)) (hn s t f j hj k hk)
  exact hv.symm.trans (congrArg (v.app t).hom hd)

end FrobeniusSplitting.RetainedCharacter
