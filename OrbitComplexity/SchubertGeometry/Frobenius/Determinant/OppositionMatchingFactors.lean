import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarColimitSquares
import Batteries.Tactic.Lint

/-! # Matching chart factors after scalar extension

Cartesian node squares give chart factors with both prescribed projections.
The diagrams and their scalar comparison are determined by the word model.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

/-- A map to an arithmetic coordinate node and a compatible map to the field
colimit lift to the prescribed field coordinate node. -/
theorem exists_retained_node_factor
    {R K : Type u} [rComm : CommRing R] [kComm : CommRing K]
    [rKAlg : Algebra R K] {J : Type u}
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, e s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x)
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (s : {s : Finset J // s.Nonempty})
    {Q : Scheme.{u}} (g : Q ⟶ Spec (.of (N.obj s)))
    (a : Q ⟶ cF.pt.left)
    (h : g ≫ (cN.ι.app (op s)).left = a ≫ qN) :
    ∃ f : Q ⟶ Spec (.of (F.obj s)),
      f ≫ Spec.map (v.app s) = g ∧ f ≫ (cF.ι.app (op s)).left = a := by
  have nodeSquare := @FrobeniusSplitting.scalarColimit_isPullback.{u,u,u}
    R K rComm kComm rKAlg {s : Finset J // s.Nonempty}
    (inferInstanceAs (Category {s : Finset J // s.Nonempty}))
    (inferInstanceAs (Quiver.IsThin {s : Finset J // s.Nonempty}))
    (inferInstanceAs (Small.{u} {s : Finset J // s.Nonempty}))
    N F (fun {_ _} f => hNopen f.unop) hNdir v e hev cN hcN cF hcF qN hqN s
  exact nodeSquare.exists_lift g a h

end SchubertGeometry.RetainedCharacter
