import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionMatchingFactors
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCommonCoframes
import Batteries.Tactic.Lint

/-! # Affine refinements on the opposition-chart preimage

The canonical affine coordinates of a preimage chart factor through its original
matching node by morphisms over the coefficient field.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting ReductiveGroups GroupActions
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter


private theorem associate_base {P Q X Y B : Scheme.{u}}
    (p : P ⟶ Q) (t : Q ⟶ X) (s : X ⟶ Y) (b : Y ⟶ B) (c : P ⟶ B)
    (h : p ≫ (t ≫ (s ≫ b)) = c) :
    ((p ≫ t) ≫ s) ≫ b = c := by
  simpa only [Category.assoc] using h

private theorem factor_over {B : Scheme.{u}} (Q X Y : Over B)
    (l : X ⟶ Y) (f : Q.left ⟶ X.left) (a : Q.left ⟶ Y.left)
    (hf : f ≫ l.left = a) (ha : a ≫ Y.hom = Q.hom) :
    f ≫ X.hom = Q.hom := by
  calc
    f ≫ X.hom = f ≫ (l.left ≫ Y.hom) := congrArg (f ≫ ·) l.w.symm
    _ = (f ≫ l.left) ≫ Y.hom := (Category.assoc _ _ _).symm
    _ = a ≫ Y.hom := congrArg (· ≫ Y.hom) hf
    _ = Q.hom := ha


open private FrobeniusSplitting.RetainedCharacter.singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private SchubertGeometry.RetainedCharacter.preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
open private SchubertGeometry.RetainedCharacter.affineChart_base from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCommonCoframes

/-- The affine coordinates of a word-chart preimage factor through the original
singleton matching chart by a morphism over the coefficient field. -/
theorem exists_affine_preimage_refinement
    {R K : Type u} [hR : CommRing R]
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [hRK : Algebra R K]
    {J : Type u}
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
    (cN : Cocone (N.op ⋙
      algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K)))
    (hcF : IsColimit cF)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (q : cF.pt.left ⟶ bsdhScheme G word) (i : G.rootBase.support)
    (P : Scheme.{u}) [hP : IsAffine P]
    (t : P ⟶ wordChartPreimage G word q i) (index : J)
    (g : Spec (.of Γ(P, ⊤)) ⟶ Spec (.of
      (N.obj
        (FrobeniusSplitting.RetainedCharacter.singletonIndex index))))
    (h : g ≫ (cN.ι.app (op
        (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left =
      ((P.isoSpec.inv ≫ t) ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ≫
        qN) :
    let : Algebra K Γ(P, ⊤) :=
      ((t ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ f : (algSpec (.of K)).obj (op (CommAlgCat.of K Γ(P, ⊤))) ⟶
        (algSpec (.of K)).obj (op (F.obj
          (FrobeniusSplitting.RetainedCharacter.singletonIndex index))),
      f.left ≫ (cF.ι.app (op
        (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left =
          (P.isoSpec.inv ≫ t) ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i := by
  let : Algebra K Γ(P, ⊤) :=
    ((t ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  obtain ⟨f, _, hf⟩ := @exists_retained_node_factor.{u}
    R K hR hK.toCommRing hRK J N F hNopen hNdir e v hev
    cN hcN cF hcF qN hqN
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index)
    (Spec (.of Γ(P, ⊤))) g
    ((P.isoSpec.inv ≫ t) ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i) h
  have hb := @SchubertGeometry.RetainedCharacter.affineChart_base K
    (inferInstanceAs (CommRing K)) P hP
    (t ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom))
  have ha := @associate_base (Spec (.of Γ(P, ⊤))) P
    (wordChartPreimage G word q i) cF.pt.left (Spec (.of K)) P.isoSpec.inv t
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) cF.pt.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ(P, ⊤)))) hb
  have hstructure := @factor_over (Spec (.of K))
    ((algSpec (.of K)).obj (op (CommAlgCat.of K Γ(P, ⊤))))
    ((algSpec (.of K)).obj (op (F.obj
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index))))
    cF.pt (cF.ι.app (op
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index))) f
    ((P.isoSpec.inv ≫ t) ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i) hf ha
  exact ⟨Over.homMk f hstructure, hf⟩

end SchubertGeometry.RetainedCharacter
