import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Arithmetic append section coordinates

The fixed affine scalar square identifies its entire ring-map square before
any coefficient is evaluated. The retained degree-one word coefficient, append
unit, and polynomial then give the arithmetic section equation for every power
on both polynomial charts. No change of the coefficient diagram is made.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private framePolynomial
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections
open private section_chart_map
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates

private theorem affine_square_maps {A B C D : CommRingCat.{u}}
    (u : A ⟶ B) (v : C ⟶ D) (a : Spec C ⟶ Spec A) (b : Spec D ⟶ Spec B)
    (h : Spec.map v ≫ a = b ≫ Spec.map u) :
    Spec.preimage a ≫ v = u ≫ Spec.preimage b := by
  have he := congrArg (fun f : Spec D ⟶ Spec A => Spec.preimage f) h
  simpa only [Spec.preimage_comp, Spec.preimage_map] using he

private theorem affine_square_ringMaps {A B C D : CommRingCat.{u}}
    (u : A ⟶ B) (v : C ⟶ D) (a : Spec C ⟶ Spec A) (b : Spec D ⟶ Spec B)
    (h : Spec.map v ≫ a = b ≫ Spec.map u) :
    v.hom.comp (Spec.preimage a).hom = (Spec.preimage b).hom.comp u.hom := by
  exact congrArg (fun f : A ⟶ D => f.hom) (affine_square_maps u v a b h)

private theorem section_reflects {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (eta : A →+* B) (v : C →+* D) (hinj : Function.Injective v)
    (a : Polynomial A →+* C) (b : Polynomial B →+* D)
    (hsquare : v.comp a = b.comp (Polynomial.mapRingHom eta))
    (r d : C) (s e : D) (hr : v r = s) (hd : v d = e)
    (P : Polynomial A) (Q : Polynomial B) (hP : Polynomial.map eta P = Q)
    (j : Fin 2) (n : ℕ)
    (hQ : (s * e) ^ n = b (sectionChartPolynomial (2 * n) (Q ^ n) j)) :
    (r * d) ^ n = a (sectionChartPolynomial (2 * n) (P ^ n) j) := by
  apply hinj
  have hp : Polynomial.map eta (P ^ n) = Q ^ n :=
    (Polynomial.map_pow eta n).trans (congrArg (fun X : Polynomial B => X ^ n) hP)
  have hc : Polynomial.map eta (sectionChartPolynomial (2 * n) (P ^ n) j) =
      sectionChartPolynomial (2 * n) (Q ^ n) j :=
    (section_chart_map eta (2 * n) (P ^ n) j).trans
      (congrArg (fun X : Polynomial B => sectionChartPolynomial (2 * n) X j) hp)
  have hs := congrArg (fun f : Polynomial A →+* D =>
    f (sectionChartPolynomial (2 * n) (P ^ n) j)) hsquare
  calc
    v ((r * d) ^ n) = (s * e) ^ n := by rw [map_pow, map_mul, hr, hd]
    _ = b (sectionChartPolynomial (2 * n) (Q ^ n) j) := hQ
    _ = b (Polynomial.map eta (sectionChartPolynomial (2 * n) (P ^ n) j)) :=
      congrArg b hc.symm
    _ = v (a (sectionChartPolynomial (2 * n) (P ^ n) j)) := hs.symm

section Append
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {J : Type u} (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i])) (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    {R : Type u} [CommRing R] [Algebra R K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)

end Append

end SchubertGeometry.RetainedCharacter
