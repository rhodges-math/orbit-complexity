import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import OrbitComplexity.FrobeniusSplitting.Normality.EquifiberedColimits
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Cartesian charts of scalar colimits

Scalar-coordinate isomorphisms make every node square Cartesian. Their
equifibered diagram then identifies each node as the inverse image of the
original chart under the colimit comparison.
-/

set_option autoImplicit false

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

open private tensor_inclusion_cart equifibered_of_cart from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
open private scalarSchemesMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarCoordinateCocone

namespace FrobeniusSplitting

private theorem pullback_precompose {C : Type*} [Category C]
    {P Q X Y Z : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (e : Q ≅ P) :
    IsPullback (e.hom ≫ a) (e.hom ≫ b) f g := by
  exact h.of_iso' e (Iso.refl X) (Iso.refl Y) (Iso.refl Z)
    (by simp) (by simp) (by simp) (by simp)

private theorem scalar_first_map {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) (f : A →+* B)
    (he : ∀ x, e ((1 : K) ⊗ₜ[R] x) = f x) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom) =
      Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext x
  exact he x

private theorem scalar_base_map {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext x
  exact e.commutes x

private theorem scalar_node_cart {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B]
    (e : K ⊗[R] A ≃ₐ[K] B) (f : A →+* B)
    (he : ∀ x, e ((1 : K) ⊗ₜ[R] x) = f x) :
    IsPullback (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (algebraMap K B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let E : Spec (.of B) ≅ Spec (.of (K ⊗[R] A)) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  have h := pullback_precompose
    (tensor_inclusion_cart (S := R) (R := K) (A := A)) E
  change IsPullback
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom))
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[R] A))))
    _ _ at h
  rw [scalar_first_map e f he, scalar_base_map e] at h
  exact h

/-- Scalar-coordinate isomorphisms identify each original chart with its
Cartesian inverse image under the comparison of the two colimits. -/
theorem scalarColimit_isPullback
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
    (N : J ⥤ CommAlgCat.{u} R) (F : J ⥤ CommAlgCat.{u} K)
    [∀ {s t : Jᵒᵖ} (f : s ⟶ t),
      IsOpenImmersion (((N.op ⋙ algSpec (.of R)).map f).left)]
    [(((N.op ⋙ algSpec (.of R)) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s x, e s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x)
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ cN.pt.left)
    (hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q) (s : J) :
    IsPullback (Spec.map (v.app s)) (cF.ι.app (op s)).left
      (cN.ι.app (op s)).left q := by
  let : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsOpenImmersion
      ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))).map f) :=
    fun {_ _} f => inferInstanceAs
      (IsOpenImmersion (((N.op ⋙ algSpec (.of R)).map f).left))
  let : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := inferInstanceAs
    ((((N.op ⋙ algSpec (.of R)) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected)
  have hcart : ∀ j : Jᵒᵖ, IsPullback
      ((scalarSchemesMap N F v).app j)
      ((F.op ⋙ algSpec (.of K)).obj j).hom
      ((N.op ⋙ algSpec (.of R)).obj j).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    intro j
    exact scalar_node_cart (e j.unop) (v.app j.unop).hom (he j.unop)
  have hα := equifibered_of_cart (F.op ⋙ algSpec (.of K))
    (N.op ⋙ algSpec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (scalarSchemesMap N F v) hcart
  exact isPullback_colimit_component
    (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K)))
    (N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (scalarSchemesMap N F v) hα
    ((Over.forget (Spec (.of K))).mapCocone cF)
    ((Over.forget (Spec (.of R))).mapCocone cN)
    (isColimitOfPreserves (Over.forget (Spec (.of K))) hcF)
    (isColimitOfPreserves (Over.forget (Spec (.of R))) hcN)
    q (fun j => (hq j.unop).symm) (op s)

end FrobeniusSplitting
