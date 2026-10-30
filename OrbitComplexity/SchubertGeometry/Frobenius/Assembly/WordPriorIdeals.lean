import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prior ideals and the twisted functional

Ideal preservation by the raw functional passes to its coframe operators
through the retained coordinate isomorphisms. The resulting polynomial-chart
splittings preserve the extended ideals.
-/

set_option autoImplicit false
noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.ProjectiveCartier

open private retainedChartRange retainedCoordinateIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

private theorem transport_ideal
    {A B : Type*} [CommRing A] [CommRing B] {p : ℕ}
    (φ : FrobeniusLinearMap A p) (e : A ≃+* B) (I : Ideal A)
    (hI : ∀ a ∈ I, φ a ∈ I) :
    ∀ b ∈ I.comap e.symm.toRingHom,
      φ.transport e b ∈ I.comap e.symm.toRingHom := by
  intro b hb
  change e.symm (e (φ (e.symm b))) ∈ I
  rw [e.symm_apply_apply]
  exact hI _ hb

variable {C R J : Type u} [CommRing C] [CommRing R]
    {p : ℕ} [ExpChar C p] [Category.{u} J] [Quiver.IsThin J]
    (N : J ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)

/-- A retained coframe operator preserves the coordinate ideal induced by an
ideal preserved by the raw functional on that frame. -/
theorem retainedTwistedPrior_ideal
    (base : cN.pt.left ⟶ Spec (.of C)) (L : cN.pt.left.Modules)
    (Θ : frobeniusRestriction C p base L ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (s : J) (frame : Γ(L, retainedChartRange N cN hcN s))
    (I : Ideal Γ(cN.pt.left, retainedChartRange N cN hcN s))
    (hI : ∀ a ∈ I, Θ.app (retainedChartRange N cN hcN s) (a • frame) ∈ I) :
    ∀ a ∈ I.comap (retainedCoordinateIso N cN hcN s).inv.hom,
      retainedTwistedPriorOperator N cN hcN base L Θ s frame a ∈
        I.comap (retainedCoordinateIso N cN hcN s).inv.hom := by
  apply transport_ideal
    (twistedFrameOperator base L Θ (retainedChartRange N cN hcN s) frame)
    (retainedCoordinateIso N cN hcN s).commRingCatIsoToRingEquiv I
  intro a ha
  exact hI a ha

end SchubertGeometry.ProjectiveCartier

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private indices from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private chartOpen from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private matchingPriorOperator from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNormalizedCharts
open private retainedChartRange retainedCoordinateIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
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
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) * (delta s j hj k hk : N.obj s))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta ((p - 1) / 2)) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))

/-- Preservation by the preceding raw matching-line functional supplies ideal
compatibility for both normalized retained polynomial charts. -/
theorem retainedMatching_prior_ideal (hp : Odd p) (j : J)
    (I : Ideal Γ(cN.pt.left, retainedChartRange N cN hcN (singletonIndex j)))
    (hI : ∀ a ∈ I,
      ∀ e : Γ(matchingModule N cN delta ((p - 1) / 2),
        retainedChartRange N cN hcN (singletonIndex j)),
      Θ.app (retainedChartRange N cN hcN (singletonIndex j)) (a • e) ∈ I)
    (k : indices.{u}) :
    let Q := I.comap (retainedCoordinateIso N cN hcN (singletonIndex j)).inv.hom
    ∃ ρ : RingSplitting (Polynomial (N.obj (singletonIndex j))) p,
      (ρ.toOperator.toSpec (expChar_pos K p)).pushforward
          (projectiveLinePolynomialIso (N.obj (singletonIndex j)) k).hom =
        (retainedMatchingSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp
            j).toOperator.restrict
          (chartOpen (N.obj (singletonIndex j)) k) ∧
      ρ.IsCompatible (Q.map Polynomial.C) := by
  let Q := I.comap (retainedCoordinateIso N cN hcN (singletonIndex j)).inv.hom
  apply retainedMatching_prior N cN hcN delta hco hn P hP hr base Θ hnorm hp j Q _ k
  exact ProjectiveCartier.retainedTwistedPrior_ideal N cN hcN base
    (matchingModule N cN delta ((p - 1) / 2)) Θ (singletonIndex j)
    (retainedMatchingFrameSection N cN hcN delta ((p - 1) / 2) hco hn
      (singletonIndex j) j (Finset.mem_singleton_self j) 1)
    I (fun a ha => hI a ha _)

end SchubertGeometry.RetainedCharacter
