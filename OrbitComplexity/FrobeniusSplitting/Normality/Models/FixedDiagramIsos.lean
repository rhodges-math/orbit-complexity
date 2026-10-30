import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Affine
import Batteries.Tactic.Lint

/-! # The retained diagram isomorphisms through coefficient enlargement -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u v w

/-- Extend the specified diagram isomorphism itself, retaining every arrow. -/
def fixedFibreDiagramIso {J : Type v} [Category.{w} J]
    {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]
    {P Q : J ⥤ CommAlgCat.{u} S} (e : P ≅ Q) :
    fixedFibreDiagram (R := R) (M := R) P ≅
      fixedFibreDiagram (R := R) (M := R) Q :=
  NatIso.ofComponents (fun i => CommAlgCat.isoMk
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
      (CommAlgCat.algEquivOfIso (e.app i))))
    (by
      intro i j f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r x =>
          change r ⊗ₜ[S] (e.hom.app j).hom ((P.map f).hom x) =
            r ⊗ₜ[S] (Q.map f).hom ((e.hom.app i).hom x)
          exact congrArg (fun z => r ⊗ₜ[S] z)
            (congrArg (fun g => g.hom x) (e.hom.naturality f))
      | add z z' hz hz' =>
          simpa only [map_add] using congrArg₂ (· + ·) hz hz')

/-- Cancellation identifies the two successive coefficient extensions
with the single extension of the original chosen diagram, on every node and arrow. -/
def fixedFibreCancelIso {J : Type v} [Category.{w} J]
    {S T R : Type u} [CommRing S] [CommRing T] [CommRing R]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    (P : J ⥤ CommAlgCat.{u} S) :
    fixedFibreDiagram (R := R) (M := R)
      (fixedFibreDiagram (R := T) (M := T) P) ≅
        fixedFibreDiagram (R := R) (M := R) P :=
  NatIso.ofComponents (fun i => CommAlgCat.isoMk
    (Algebra.TensorProduct.cancelBaseChange S T R R (P.obj i))) (by
      intro i j f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul r z =>
          induction z using TensorProduct.inductionOn with
          | tmul t x =>
              simp [fixedFibreDiagram, Algebra.TensorProduct.cancelBaseChange_tmul]
          | add z z' hz hz' =>
              simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hz'
      | add z z' hz hz' =>
          simpa only [map_add] using congrArg₂ (· + ·) hz hz')

/-- Put the specified model cocone on the original diagram through the retained
isomorphism, without changing its scheme or structural morphism. -/
def transportModelCocone {J : Type v} [Category.{w} J]
    {R : Type u} [CommRing R] {P N : J ⥤ CommAlgCat.{u} R}
    (e : P ≅ N) (c : Cocone (N.op ⋙ algSpec (.of R))) :
    Cocone (P.op ⋙ algSpec (.of R)) :=
  (Cocone.precompose
    (Functor.isoWhiskerRight (NatIso.op e.symm) (algSpec (.of R))).hom).obj c

/-- Transport preserves the colimit and open cover, including coverage
after every scheme base change. -/
theorem transportModelCocone_properties {J : Type v} [Category.{w} J]
    {R : Type u} [CommRing R] {P N : J ⥤ CommAlgCat.{u} R}
    (e : P ≅ N) (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c)
    (ho : ∀ s, IsOpenImmersion (c.ι.app s).left)
    (hcover : ∀ (T : Scheme.{u}) (f : T ⟶ c.pt.left) (y : T),
      ∃ s, ∃ z : (pullback f (c.ι.app s).left : Scheme.{u}),
        (pullback.fst f (c.ι.app s).left) z = y) :
    Nonempty (IsColimit (transportModelCocone e c)) ∧
    (∀ s, IsOpenImmersion ((transportModelCocone e c).ι.app s).left) ∧
    ∀ (T : Scheme.{u}) (f : T ⟶ (transportModelCocone e c).pt.left) (y : T),
      ∃ s, ∃ z : (pullback f ((transportModelCocone e c).ι.app s).left : Scheme.{u}),
        (pullback.fst f ((transportModelCocone e c).ι.app s).left) z = y := by
  let δ := Functor.isoWhiskerRight (NatIso.op e.symm) (algSpec (.of R))
  refine ⟨⟨(IsColimit.precomposeHomEquiv δ c).symm hc⟩, ?_, ?_⟩
  · intro s
    have : IsOpenImmersion (c.ι.app s).left := ho s
    change IsOpenImmersion ((δ.hom.app s).left ≫ (c.ι.app s).left)
    infer_instance
  · intro T f y
    obtain ⟨s, z, hz⟩ := hcover T f y
    let a := (Over.forget (Spec (.of R))).mapIso (δ.app s)
    have ha : (c.ι.app s).left ≫ 𝟙 c.pt.left =
        a.inv ≫ ((transportModelCocone e c).ι.app s).left := by
      change (c.ι.app s).left ≫ 𝟙 _ = a.inv ≫ (a.hom ≫ (c.ι.app s).left)
      simp
    let v := pullback.map f (c.ι.app s).left f
      ((transportModelCocone e c).ι.app s).left (𝟙 T) a.inv (𝟙 c.pt.left)
      (by exact (Category.comp_id f).trans (Category.id_comp f).symm) ha
    refine ⟨s, v z, ?_⟩
    have hv : v ≫ pullback.fst f ((transportModelCocone e c).ι.app s).left =
        pullback.fst f (c.ι.app s).left := by simp [v]
    change (v ≫ pullback.fst f ((transportModelCocone e c).ι.app s).left) z = y
    rw [hv]
    exact hz

end
end FrobeniusSplitting
