import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficient extension of a fixed model and its field comparison

The coefficient cocone is extended while retaining every leg into the
preceding model. Its universal property transports the prescribed field
comparison through the same extension.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

open private comparison_lift coefficient_base_factor from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendAtlas

/-- Extend a fixed coefficient cocone and retain its preceding chart legs,
field comparison and both structure maps. -/
theorem exists_fixed_scalar_comparison {J : Type v} [Category.{w} J]
    [Quiver.IsThin J] [Small.{u} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra T K] [Algebra S K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S)
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j),
      IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left)]
    [(((N.op ⋙ algSpec (.of S)) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    {YK : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (hm : IsPullback m baseK cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    let NT := fixedFibreDiagram (R := T) (M := T) N
    (∀ {i j : Jᵒᵖ} (f : i ⟶ j),
      IsOpenImmersion (((NT.op ⋙ algSpec (.of T)).map f).left)) ∧
      ((((NT.op ⋙ algSpec (.of T)) ⋙ Over.forget (Spec (.of T))) ⋙
        Scheme.forget).IsLocallyDirected) ∧
      ∃ (cT : Cocone (NT.op ⋙ algSpec (.of T)))
        (q : cT.pt.left ⟶ cN.pt.left) (n : YK ⟶ cT.pt.left),
        Nonempty (IsColimit cT) ∧
          IsPullback q cT.pt.hom cN.pt.hom
            (Spec.map (CommRingCat.ofHom (algebraMap S T))) ∧
          IsPullback n baseK cT.pt.hom
            (Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
          n ≫ q = m ∧ n ≫ cT.pt.hom =
            baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap T K)) ∧
          ∀ i, (cT.ι.app i).left ≫ q = Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : N.obj i.unop →ₐ[S]
              T ⊗[S] N.obj i.unop).toRingHom) ≫ (cN.ι.app i).left := by
  obtain ⟨ho, hd, cT, q, hcT, hq, hlegs⟩ :=
    exists_fixed_scalar_cocone (R := T) N cN hcN
  obtain ⟨n, hnq, hnb, hn⟩ := comparison_lift
    (Spec.map (CommRingCat.ofHom (algebraMap S T)))
    (Spec.map (CommRingCat.ofHom (algebraMap T K)))
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (coefficient_base_factor (R := T)) cN.pt.hom cT.pt.hom q hq baseK m hm
  exact ⟨ho, hd, cT, q, n, hcT, hq, hn, hnq, hnb, hlegs⟩

end SchubertGeometry
