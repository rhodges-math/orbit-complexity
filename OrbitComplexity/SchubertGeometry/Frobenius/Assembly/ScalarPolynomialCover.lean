import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialComparison
import Batteries.Tactic.Lint

/-! # Polynomial covers through a coefficient extension

The scalar cover uses the same coefficient rings and the same field chart
maps. Its coordinate and field squares retain both projections into the
preceding model.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SchubertGeometry

private theorem iso_chart_projection {C : Type v} [Category.{w} C]
    {P V Y X : C} (e : V ≅ P) (f : V ⟶ Y) (q : Y ⟶ X) (g : P ⟶ X)
    (h : f ≫ q = e.hom ≫ g) : (e.inv ≫ f) ≫ q = g := by
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem iso_chart_square {C : Type v} [Category.{w} C]
    {P V PK Y Z : C} (e : V ≅ P) (k : PK ⟶ P)
    (j : PK ⟶ Z) (f : V ⟶ Y) (n : Z ⟶ Y)
    (h : IsPullback k j (e.inv ≫ f) n) :
    IsPullback (k ≫ e.inv) j f n := by
  have he : IsPullback e.inv (e.inv ≫ f) f (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id]⟩
  simpa only [Category.comp_id] using h.paste_horiz he

section Cover

variable {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
  [Algebra S T] [Algebra T K] [Algebra S K] [IsScalarTower S T K]

private abbrev oldMap {A : Type u} [CommRing A] [Algebra S A] :
    Spec (.of (Polynomial (T ⊗[S] A))) ⟶ Spec (.of (Polynomial A)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom))

private abbrev fieldMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra S A] [Algebra K B] (e : K ⊗[S] A ≃ₐ[K] B) :
    Spec (.of (Polynomial B)) ⟶ Spec (.of (Polynomial (T ⊗[S] A))) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (((Algebra.TensorProduct.cancelBaseChange S T K K A).trans e).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)))

/-- Extend a finite polynomial cover and construct its Cartesian comparison
with the prescribed field charts, preserving their coefficient maps. -/
theorem exists_scalar_polynomial_cover {X Y Z : Scheme.{u}}
    (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (baseK : Z ⟶ Spec (.of K)) (q : Y ⟶ X) (n : Z ⟶ Y) (m : Z ⟶ X)
    (hq : IsPullback q baseT base
      (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : IsPullback n baseK baseT
      (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (hm : IsPullback m baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (hnq : n ≫ q = m)
    (U : X.OpenCover.{u}) [Finite U.I₀]
    (A : U.I₀ → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra S (A i)]
    (eU : ∀ i, U.X i ≅ Spec (.of (Polynomial (A i))))
    (hU : ∀ i, ((eU i).inv ≫ U.f i) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A i)))))
    (B : U.I₀ → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    (e : ∀ i, K ⊗[S] A i ≃ₐ[K] B i)
    (jK : ∀ i, Spec (.of (Polynomial (B i))) ⟶ Z)
    (hjK : ∀ i, jK i ≫ m = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e i).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ (eU i).inv ≫ U.f i)
    (hjKb : ∀ i, jK i ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (B i))))) :
    ∃ (V : Y.OpenCover.{u}) (_hfinite : Finite V.I₀) (_haffine : ∀ i, IsAffine (V.X i))
      (index : V.I₀ ≃ U.I₀)
      (eV : ∀ i, V.X i ≅ Spec (.of (Polynomial (T ⊗[S] A (index i))))),
      (∀ i, IsPullback ((eV i).hom ≫ oldMap) (V.f i)
        ((eU (index i)).inv ≫ U.f (index i)) q) ∧
      (∀ i, V.f i ≫ baseT = (eV i).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A (index i)))))) ∧
      (∀ i, V.f i ≫ q = (eV i).hom ≫ oldMap ≫
        (eU (index i)).inv ≫ U.f (index i)) ∧
      (∀ i, IsPullback (fieldMap (e (index i))) (jK (index i))
        ((eV i).inv ≫ V.f i) n) ∧
      (∀ i, IsPullback (fieldMap (e (index i)) ≫ (eV i).inv)
        (jK (index i)) (V.f i) n) ∧
      ∀ i, jK (index i) ≫ n =
        fieldMap (e (index i)) ≫ (eV i).inv ≫ V.f i := by
  obtain ⟨V, hfinite, haffine, index, eV, hcart, hbase, hold⟩ :=
    exists_append_scalar_cover base baseT q hq U A eU hU
  have hf (i : V.I₀) : IsPullback (fieldMap (e (index i))) (jK (index i))
      ((eV i).inv ≫ V.f i) n ∧
      jK (index i) ≫ n = fieldMap (e (index i)) ≫ (eV i).inv ≫ V.f i := by
    exact scalarPolynomial_field_chart (e (index i)) q n m base baseT baseK hn hm hnq
      ((eU (index i)).inv ≫ U.f (index i)) ((eV i).inv ≫ V.f i) (jK (index i))
      (iso_chart_projection (eV i) (V.f i) q _ (hold i))
      (iso_chart_projection (eV i) (V.f i) baseT _ (hbase i))
      (by simpa only [Category.assoc] using hjK (index i)) (hjKb (index i))
  exact ⟨V, hfinite, haffine, index, eV, hcart, hbase, hold,
    fun i => (hf i).1,
    fun i => iso_chart_square (eV i) _ _ _ n (hf i).1,
    fun i => (hf i).2⟩

end Cover

end SchubertGeometry
