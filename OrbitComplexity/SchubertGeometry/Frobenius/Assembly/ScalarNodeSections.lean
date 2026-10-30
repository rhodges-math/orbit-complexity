import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section coordinates on scalar projective nodes

The polynomial cover of a scalar model retains its original projective-node
index and both projections. These equations identify its polynomial
maps with the two charts of the scalar projective nodes. Section coframes and
their polynomial coordinates then give coframes on every node chart.
-/

set_option autoImplicit false

noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GroupActions Polynomial
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private coefficient nodeBase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem inverse_projection {C : Type*} [Category C]
    {U P X B : C} (e : U ≅ P) (a : U ⟶ X) (q : X ⟶ B)
    (b : P ⟶ B) (h : a ≫ q = e.hom ≫ b) :
    (e.inv ≫ a) ≫ q = b := by
  calc
    (e.inv ≫ a) ≫ q = e.inv ≫ (a ≫ q) := Category.assoc _ _ _
    _ = e.inv ≫ (e.hom ≫ b) := congrArg (fun f => e.inv ≫ f) h
    _ = b := Iso.inv_hom_id_assoc e b

private theorem equal_map_section {P X : Scheme.{u}} (a b : P ⟶ X)
    (h : a = b) (L : X.Modules) (m : unitModule X ⟶ L)
    (F : (Scheme.Modules.pullback b).obj L ≅ unitModule P)
    (z : Γ(P, ⊤)) (hs : sectionValue b L m F.hom z) :
    ∃ E : (Scheme.Modules.pullback a).obj L ≅ unitModule P,
      sectionValue a L m E.hom z := by
  subst b
  exact ⟨F, hs⟩

section Cover

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {J : Type v} (A : J → CommAlgCat.{u} S)
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of S)) (baseT : Y ⟶ Spec (.of T))
    (q : Y ⟶ X)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (old : ∀ s, line (A s) ⟶ X)
    (K : ∀ s, line (T ⊗[S] A s) ⟶ Y)
    (hOld : ∀ s, K s ≫ q = coefficient S T (A s) ≫ old s)
    (hBase : ∀ s, K s ≫ baseT = nodeBase S T (A s))
    (V : Y.OpenCover.{u})
    (index : V.I₀ ≃ J × ULift.{u} (Fin 2))
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (T ⊗[S] A (index z).1))))
    (hold : ∀ z, V.f z ≫ q = (eV z).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight :
          A (index z).1 →ₐ[S] T ⊗[S] A (index z).1).toRingHom)) ≫
        projectiveLinePolynomialChart (A (index z).1) (index z).2 ≫ old (index z).1)
    (hbase : ∀ z, V.f z ≫ baseT = (eV z).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap T (Polynomial (T ⊗[S] A (index z).1)))))

include hq hOld hBase hold hbase in
/-- The polynomial maps of the retained cover are the polynomial
charts of its prescribed scalar projective nodes. -/
theorem scalarCover_node_chart (z : V.I₀) :
    projectiveLinePolynomialChart (T ⊗[S] A (index z).1) (index z).2 ≫
      K (index z).1 = (eV z).inv ≫ V.f z := by
  exact scalarProjective_polynomial_chart base baseT q hq
    (old (index z).1) (K (index z).1) (hOld (index z).1) (hBase (index z).1)
    (index z).2 ((eV z).inv ≫ V.f z)
    (inverse_projection (eV z) (V.f z) q _ (hold z))
    (inverse_projection (eV z) (V.f z) baseT _ (hbase z))

include hq hOld hBase hold hbase in
/-- Coordinates of one section on the retained polynomial cover supply
coframes and the same homogeneous coordinates on both charts of every scalar
projective node, without changing the model or its node maps. -/
theorem scalarCover_node_sections (L : Y.Modules) (m : unitModule Y ⟶ L)
    (F : ∀ z, (Scheme.Modules.pullback ((eV z).inv ≫ V.f z)).obj L ≅
      unitModule (Spec (.of (Polynomial (T ⊗[S] A (index z).1)))))
    (d : ℕ) (P : ∀ s, Polynomial (T ⊗[S] A s))
    (hsections : ∀ z, sectionValue ((eV z).inv ≫ V.f z) L m (F z).hom
      ((Scheme.ΓSpecIso (.of (Polynomial (T ⊗[S] A (index z).1)))).inv
        (sectionChartPolynomial d (P (index z).1) (index z).2.down))) :
    ∃ E : ∀ s (j : ULift.{u} (Fin 2)),
      (Scheme.Modules.pullback
        (projectiveLinePolynomialChart (T ⊗[S] A s) j ≫ K s)).obj L ≅
          unitModule (Spec (.of (Polynomial (T ⊗[S] A s)))),
      ∀ s j, sectionValue
        (projectiveLinePolynomialChart (T ⊗[S] A s) j ≫ K s) L m (E s j).hom
        ((Scheme.ΓSpecIso (.of (Polynomial (T ⊗[S] A s)))).inv
          (sectionChartPolynomial d (P s) j.down)) := by
  classical
  have hcoords : ∀ s (j : ULift.{u} (Fin 2)),
      ∃ E : (Scheme.Modules.pullback
        (projectiveLinePolynomialChart (T ⊗[S] A s) j ≫ K s)).obj L ≅
          unitModule (Spec (.of (Polynomial (T ⊗[S] A s)))),
        sectionValue (projectiveLinePolynomialChart (T ⊗[S] A s) j ≫ K s)
          L m E.hom ((Scheme.ΓSpecIso (.of (Polynomial (T ⊗[S] A s)))).inv
            (sectionChartPolynomial d (P s) j.down)) := by
    intro s j
    obtain ⟨z, hz⟩ := index.surjective (s, j)
    have hs : (index z).1 = s := congrArg Prod.fst hz
    have hj : (index z).2 = j := congrArg Prod.snd hz
    subst s
    subst j
    exact equal_map_section _ _
      (scalarCover_node_chart A base baseT q hq old K hOld hBase V index eV hold hbase z)
      L m (F z) _ (hsections z)
  choose E hE using hcoords
  exact ⟨E, hE⟩

end Cover

end SchubertGeometry.RetainedCharacter
