import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialCovariance
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Transition agreement for the normalized word nodes

The two polynomial values are values of one global matching section. Its chart
triangle, transported highest coefficients, and the preceding-word
normalization determine full polynomial covariance and hence Cartier agreement.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private quadratic_degree from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCompatibleSplitting
open private affinePolynomialMap projectiveRefinement projectiveRefinement_open
  projectiveOperatorMapData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private nodePrior nodePrior_normalized from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private line from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private pullback_eq_of_hom_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

private theorem quadraticPower_coeff {A B : Type u} [CommRing A] [CommRing B]
    (P : Polynomial A) (hP : P.natDegree ≤ 2) (f : A →+* B) (p : ℕ) (hp : Odd p) :
    ((Polynomial.map f P) ^ ((p - 1) / 2)).coeff (p - 1) =
      (f (P.coeff 2)) ^ ((p - 1) / 2) := by
  have hhalf : ((p - 1) / 2) * 2 = p - 1 := by
    obtain ⟨m, hm⟩ := hp.exists_bit1
    omega
  have hd : (Polynomial.map f P).natDegree ≤ 2 := Polynomial.natDegree_map_le.trans hP
  calc
    _ = ((Polynomial.map f P) ^ ((p - 1) / 2)).coeff (((p - 1) / 2) * 2) :=
      congrArg (fun i => ((Polynomial.map f P) ^ ((p - 1) / 2)).coeff i) hhalf.symm
    _ = ((Polynomial.map f P).coeff 2) ^ ((p - 1) / 2) :=
      Polynomial.coeff_pow_of_natDegree_le hd
    _ = _ := by rw [Polynomial.coeff_map]

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

/-- The constructed normalized node operators agree under the prescribed
projective transition. Full polynomial covariance follows internally from the
same global section and its ordinary chart/coframe values. -/
theorem retainedNodeSplitting_refine (hp : Odd p) (hp' : 1 < p)
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t)
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ t.val)
    (a : (N.obj t)ˣ) (b : N.obj t)
    (Z : Scheme.{u}) (L : Z.Modules) (m : SheafOfModules.unit Z.ringCatSheaf ⟶ L)
    (u : Spec (.of (Polynomial (N.obj s))) ⟶ Z)
    (v : Spec (.of (Polynomial (N.obj t))) ⟶ Z)
    (htriangle : v = Spec.map (CommRingCat.ofHom
      (affinePolynomialMap (N.map f).hom.toRingHom a b)) ≫ u)
    (E : (Scheme.Modules.pullback u).obj L ≅
      SheafOfModules.unit (Spec (.of (Polynomial (N.obj s)))).ringCatSheaf)
    (F : (Scheme.Modules.pullback v).obj L ≅
      SheafOfModules.unit (Spec (.of (Polynomial (N.obj t)))).ringCatSheaf)
    (hs : sectionValue u L m E.hom ((Scheme.ΓSpecIso (.of (Polynomial (N.obj s)))).inv
      ((Polynomial.map (N.map (singletonArrow s j hj)).hom.toRingHom (P j)) ^ ((p - 1) / 2))))
    (ht : sectionValue v L m F.hom ((Scheme.ΓSpecIso (.of (Polynomial (N.obj t)))).inv
      ((Polynomial.map (N.map (singletonArrow t k hk)).hom.toRingHom (P k)) ^ ((p - 1) / 2)))) :
    let : IsOpenImmersion (projectiveRefinement (N.map f).hom.toRingHom a b) :=
      projectiveRefinement_open (N.map f).hom.toRingHom a b
    ((retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp s j
        hj).toOperator).openPullback (projectiveRefinement (N.map f).hom.toRingHom a b) =
      (retainedNodeSplitting N cN hcN delta hco hn P hP hr base Θ hnorm hp t k hk).toOperator := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let : Algebra K (N.obj t) :=
    ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
  let W := (Polynomial.map (N.map (singletonArrow s j hj)).hom.toRingHom (P j)) ^ ((p - 1) / 2)
  let V := (Polynomial.map (N.map (singletonArrow t k hk)).hom.toRingHom (P k)) ^ ((p - 1) / 2)
  have hW : W.natDegree ≤ p - 1 := quadratic_degree (P j) (hP j) _ p hp
  have hV : V.natDegree ≤ p - 1 := quadratic_degree (P k) (hP k) _ p hp
  let r := (N.map (singletonArrow s j hj)).hom ((P j).coeff 2)
  let z := (N.map (singletonArrow t k hk)).hom ((P k).coeff 2)
  let d := delta t j ((leOfHom f) hj) k hk
  have harrow : singletonArrow s j hj ≫ f = singletonArrow t j ((leOfHom f) hj) :=
    Subsingleton.elim _ _
  have hmap₁ := congrArg
    (fun h : N.obj (singletonIndex j) ⟶ N.obj t => h.hom ((P j).coeff 2))
    (N.map_comp (singletonArrow s j hj) f)
  have hmap₂ := congrArg
    (fun h : singletonIndex j ⟶ t => (N.map h).hom ((P j).coeff 2)) harrow
  have hr' : (N.map f).hom r = (d : N.obj t) * z :=
    hmap₁.symm.trans (hmap₂.trans ((hr t j ((leOfHom f) hj) k hk).trans (mul_comm _ _)))
  have hWcoeff : W.coeff (p - 1) = (r * (↑(1 : (N.obj s)ˣ) : N.obj s)) ^ ((p - 1) / 2) := by
    have hc₀ := quadraticPower_coeff (P j) (hP j)
      (N.map (singletonArrow s j hj)).hom.toRingHom p hp
    have hr₀ : (N.map (singletonArrow s j hj)).hom.toRingHom ((P j).coeff 2) = r := rfl
    have hc : W.coeff (p - 1) = r ^ ((p - 1) / 2) :=
      hc₀.trans (congrArg (fun x : N.obj s => x ^ ((p - 1) / 2)) hr₀)
    simpa only [Units.val_one, mul_one] using hc
  have hVcoeff : V.coeff (p - 1) = (z * (↑(1 : (N.obj t)ˣ) : N.obj t)) ^ ((p - 1) / 2) := by
    have hc₀ := quadraticPower_coeff (P k) (hP k)
      (N.map (singletonArrow t k hk)).hom.toRingHom p hp
    have hz₀ : (N.map (singletonArrow t k hk)).hom.toRingHom ((P k).coeff 2) = z := rfl
    have hc : V.coeff (p - 1) = z ^ ((p - 1) / 2) :=
      hc₀.trans (congrArg (fun x : N.obj t => x ^ ((p - 1) / 2)) hz₀)
    simpa only [Units.val_one, mul_one] using hc
  have hnormal : nodePrior N cN hcN delta hco hn base Θ t k hk
      ((z * (↑(1 : (N.obj t)ˣ) : N.obj t)) ^ ((p - 1) / 2)) = 1 := by
    simpa only [z, Units.val_one, mul_one] using
      nodePrior_normalized N cN hcN delta hco hn P hr base Θ hnorm t k hk
  have hsection := matchingPolynomial_covariance (N.map f).hom.toRingHom
    (nodePrior N cN hcN delta hco hn base Θ t k hk) hp' r z d 1 1 ((p - 1) / 2)
    hr' W V (Polynomial.natDegree_map_le.trans hW) hWcoeff hVcoeff hnormal
    a b Z L m u v htriangle E F hs ht
  have hdata := retainedCartier_refine N cN hcN delta ((p - 1) / 2) hco hn base Θ
    f j hj k hk 1 1 (Nat.lt_trans Nat.zero_lt_one hp') a b W V hW hV hsection
  obtain ⟨g, hg, hgeq, _, hraw⟩ := hdata
  let _ := hg
  let : IsOpenImmersion (projectiveRefinement (N.map f).hom.toRingHom a b) :=
    projectiveRefinement_open (N.map f).hom.toRingHom a b
  have hS := retainedNodeSplitting_operator N cN hcN delta hco hn P hP hr base Θ hnorm hp s j hj
  have hT := retainedNodeSplitting_operator N cN hcN delta hco hn P hP hr base Θ hnorm hp t k hk
  let ψS : SchemeFrobeniusMap (line (N.obj s)) p :=
    ProjectiveCartier.relativeCartierOperator (K := K)
      (nodePrior N cN hcN delta hco hn base Θ s j hj)
      (insertedInfinity (ProjectiveLine.projectivePolynomialSection (N.obj s) (p - 1) W hW))
  have hchange := @pullback_eq_of_hom_eq p _ _ ψS
    (projectiveRefinement (N.map f).hom.toRingHom a b) g inferInstance hg hgeq.symm
  have hraw' := hchange.trans hraw
  exact (congrArg (fun Q : SchemeFrobeniusMap (line (N.obj s)) p => Q.openPullback
    (projectiveRefinement (N.map f).hom.toRingHom a b)) hS).trans (hraw'.trans hT.symm)

end SchubertGeometry.RetainedCharacter
