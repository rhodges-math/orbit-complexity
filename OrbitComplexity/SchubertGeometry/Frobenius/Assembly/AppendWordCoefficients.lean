import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAppendCoefficients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word lines and coefficients on an append model

The append atlas, the next word character line and its determinant-section
powers are retained with the preceding matching coefficients at one common
coefficient stage.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

universe u

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private extended_atlas_word map_exists_witness from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel

private theorem map_coefficient_tail {P Q R Q' : Prop}
    (h : P ∧ Q ∧ R) (f : P → Q → Q') : P ∧ Q' ∧ R :=
  ⟨h.1, f h.1 h.2.1, h.2.2⟩

/-- A common coefficient stage carries the projective append atlas, the next
word character line and every determinant-section power, together with the
preceding matching units and quadratic coefficients on that same stage. -/
theorem exists_append_word_coefficients {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {J : Type u} (V₀ : J → Over (Spec (.of K)))
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    [nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [nDir : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hchart : ∀ s j hj k hk,
      (p s j hj ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c j =
      (overlapTwist (Y := (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) (beta s j hj k hk)).hom ≫
        (p s k hk ⊗ₘ 𝟙 _) ≫ c k)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk)
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (hb : IsColimit (Cocone.mk (bsdhScheme G word) b))
    (hbbase : ∀ s, b.app (op s) ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hcart : ∀ s, IsPullback
      (fst ((algSpec (.of K)).obj (op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (op s)) (bsdhAppendFst G word i))
    (cG : Cocone (N.op ⋙ algSpec (.of S)))
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hbmodel : ∀ s, b.app (op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (op s)).left)
    [finiteJ : Finite J]
    [nodeFP : ∀ s, Algebra.FinitePresentation S (N.obj s)]
    [nodeSmooth : ∀ s, Algebra.Smooth S (N.obj s)]
    [baseProper : IsProper cG.pt.hom] [baseSmooth : Smooth cG.pt.hom]
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hP : ∀ j, (P j).natDegree ≤ 2)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) *
          (delta s j hj k hk : N.obj s))
    (hcG : IsColimit cG) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ extendedAppendWordSpec S G word i V₀ F N e p c beta sel b cG m₀ T hST ∧
        appendCoefficientSpec (R := T) N F e delta P := by
  have h := @exists_retained_append_coefficients.{u} K kField kClosed kZero S hS
    G word i J V₀ F N e he fOpen fDir nOpen nDir p c hpn beta
    hchart hnatural hbeta sel b hb hbbase hcart cG m₀ hm₀ hbmodel
    finiteJ nodeFP nodeSmooth delta hco hn P hP hr hcG
  apply map_exists_witness h
  intro T h
  apply map_exists_witness h
  intro hST h
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  apply map_coefficient_tail h
  intro hT hAtlas
  exact extended_atlas_word S G word i V₀ F N e p c beta sel b cG m₀ T hST hT hAtlas

end SchubertGeometry
