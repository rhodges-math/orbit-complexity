import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingDiagramTransport
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.TensorCancellation
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The recursive Cartier functional on the retained prior model

Canonical coefficient cancellation transports the original recursive functional
on the same cocone point. Its coefficient section and raw boundary invariants
therefore give the prior input of the retained append construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private twistModuleMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private AppendChartData AppendChartData.I AppendChartData.N from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
namespace SchubertGeometry.RetainedCharacter

private theorem prior_map_value {C : Type u} [cComm : CommRing C]
    {p : ℕ} [cChar : ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) {L M : X.Modules} (e : L ⟶ M)
    (Theta : frobeniusRestriction C p base M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (x : Γ(L, U)) :
    (@twistModuleMap.{u} C cComm p cChar X base L M e ≫ Theta).app U x =
      Theta.app U (e.app U x) := rfl

private theorem prior_map_normalized {C : Type u} [cComm : CommRing C]
    {p : ℕ} [cChar : ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) {L M : X.Modules} (e : L ⟶ M)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ M) (hs : s ≫ e = t)
    (Theta : frobeniusRestriction C p base M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hnorm : Theta.app ⊤ (Scheme.Modules.Hom.app t ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))) :
    (@twistModuleMap.{u} C cComm p cChar X base L M e ≫ Theta).app ⊤
      (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) := by
  have hvalue := congrArg
    (fun a : SheafOfModules.unit X.ringCatSheaf ⟶ M =>
      (a.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) hs
  change e.app ⊤ (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))) = Scheme.Modules.Hom.app t ⊤ (1 : Γ(X,
      ⊤)) at hvalue
  exact (prior_map_value base e Theta ⊤ (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤)))).trans
    ((congrArg (Theta.app ⊤) hvalue).trans hnorm)

private theorem prior_map_boundary {C : Type u} [cComm : CommRing C]
    {p : ℕ} [cChar : ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) {L M : X.Modules} (e : L ⟶ M)
    (Theta : frobeniusRestriction C p base M ⟶ SheafOfModules.unit X.ringCatSheaf)
    {I : Type v} (B : I → Over X)
    (hI : ∀ i (U : X.Opens) (r : Γ(X, U)), (B i).hom.app U r = 0 →
      ∀ x : Γ(M, U), (B i).hom.app U (Theta.app U (r • x)) = 0) :
    ∀ i (U : X.Opens) (r : Γ(X, U)), (B i).hom.app U r = 0 →
      ∀ x : Γ(L, U), (B i).hom.app U
        ((@twistModuleMap.{u} C cComm p cChar X base L M e ≫ Theta).app U (r • x)) = 0 := by
  intro i U r hr x
  have hvalue := prior_map_value base e Theta U (r • x)
  have hsmul := Scheme.Modules.Hom.app_smul e r x
  exact (congrArg ((B i).hom.app U)
    (hvalue.trans (congrArg (Theta.app U) hsmul))).trans
      (hI i U r hr (e.app U x))


private theorem scalar_unit_comparison {R κ J : Type u}
    [rComm : CommRing R] [κComm : CommRing κ]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (M F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ)
    (mu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (nu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (e : M ≅ F)
    (hmap : mu ≫ @matchingIsoRingMap.{u,u,u} κ κComm
      {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
          (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
          (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) M F e = nu)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) :
    ∀ s j hj k hk,
      ((@matchingIsoRingMap.{u,u,u} κ κComm {s : Finset J // s.Nonempty}
        (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
            (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s =>
            s.Nonempty))) M F e).app s).hom
          (@matchingScalarUnits.{u} R κ J rComm κComm N M mu delta s j hj k hk : M.obj s) =
        (@matchingScalarUnits.{u} R κ J rComm κComm N F nu delta s j hj k hk : F.obj s) := by
  intro s j hj k hk
  exact congrArg
    (fun a : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat κ) CommRingCat =>
      (a.app s).hom (delta s j hj k hk : N.obj s)) hmap

private theorem scalar_coefficient_comparison {R κ J : Type u}
    [rComm : CommRing R] [κComm : CommRing κ]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (M F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ)
    (mu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (nu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (e : M ≅ F)
    (hmap : mu ≫ @matchingIsoRingMap.{u,u,u} κ κComm
      {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
          (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
          (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) M F e = nu)
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) :
    ∀ j, ((@matchingIsoRingMap.{u,u,u} κ κComm {s : Finset J // s.Nonempty}
      (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
          (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s => s.Nonempty)))
          M F e).app (singletonIndex j)).hom
        ((@matchingScalarPolynomial.{u} R κ J rComm κComm N M mu P j).coeff 2) =
      (@matchingScalarPolynomial.{u} R κ J rComm κComm N F nu P j).coeff 2 := by
  intro j
  change ((@matchingIsoRingMap.{u,u,u} κ κComm {s : Finset J // s.Nonempty}
      (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
          (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s => s.Nonempty)))
          M F e).app (singletonIndex j)).hom
      ((Polynomial.map (mu.app (singletonIndex j)).hom (P j)).coeff 2) =
    (Polynomial.map (nu.app (singletonIndex j)).hom (P j)).coeff 2
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  exact congrArg
    (fun a : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat κ) CommRingCat =>
        (a.app (singletonIndex j)).hom ((P j).coeff 2)) hmap


private theorem three_scalar_maps {R S T κ J : Type u}
    [rComm : CommRing R] [sComm : CommRing S] [tComm : CommRing T]
    [κComm : CommRing κ] [rSAlg : Algebra R S] [sTAlg : Algebra S T]
    [tκAlg : Algebra T κ] [sκAlg : Algebra S κ] [rκAlg : Algebra R κ]
    [sTκ : IsScalarTower S T κ] [rSκ : IsScalarTower R S κ]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R) :
    let jCat : Category.{u} {s : Finset J // s.Nonempty} := (@Preorder.smallCategory {s : Finset J
        // s.Nonempty} (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
        (@Finset.instPartialOrder J)) (fun s => s.Nonempty)))
    let sSelf : Algebra S S := @Algebra.id S (@CommRing.toCommSemiring S sComm)
    let tSelf : Algebra T T := @Algebra.id T (@CommRing.toCommSemiring T tComm)
    let κSelf : Algebra κ κ := @Algebra.id κ (@CommRing.toCommSemiring κ κComm)
    let rSS : IsScalarTower R S S := @IsScalarTower.right R S
      (@CommRing.toCommSemiring R rComm) (@Ring.toSemiring S (@CommRing.toRing S sComm)) rSAlg
    let sTT : IsScalarTower S T T := @IsScalarTower.right S T
      (@CommRing.toCommSemiring S sComm) (@Ring.toSemiring T (@CommRing.toRing T tComm)) sTAlg
    let tκκ : IsScalarTower T κ κ := @IsScalarTower.right T κ
      (@CommRing.toCommSemiring T tComm) (@Ring.toSemiring κ (@CommRing.toRing κ κComm)) tκAlg
    let rκκ : IsScalarTower R κ κ := @IsScalarTower.right R κ
      (@CommRing.toCommSemiring R rComm) (@Ring.toSemiring κ (@CommRing.toRing κ κComm)) rκAlg
    let NS := @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} jCat
      R S S rComm sComm sComm rSAlg sSelf rSAlg rSS N
    let NST := @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} jCat
      S T T sComm tComm tComm sTAlg tSelf sTAlg sTT NS
    let NK := @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} jCat
      T κ κ tComm κComm κComm tκAlg κSelf tκAlg tκκ NST
    let ND := @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} jCat
      R κ κ rComm κComm κComm rκAlg κSelf rκAlg rκκ N
    let sκκ : IsScalarTower S κ κ := @IsScalarTower.right S κ
      (@CommRing.toCommSemiring S sComm) (@Ring.toSemiring κ (@CommRing.toRing κ κComm)) sκAlg
    let middle := @fixedFibreDiagram.{u,u,u} {s : Finset J // s.Nonempty} jCat
      S κ κ sComm κComm κComm sκAlg κSelf sκAlg sκκ NS
    let eFirst : NK ≅ middle := @tensorCancellationIso.{u,u,u} S T κ sComm tComm κComm
      sTAlg tκAlg sκAlg sTκ {s : Finset J // s.Nonempty} jCat NS
    let eSecond : middle ≅ ND := @tensorCancellationIso.{u,u,u} R S κ rComm sComm κComm
      rSAlg sκAlg rκAlg rSκ {s : Finset J // s.Nonempty} jCat N
    let diagramCategory : Category.{u} ({s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ) :=
      @Functor.category.{u,u,u,u+1} {s : Finset J // s.Nonempty} jCat
        (CommAlgCat.{u} κ) (@CommAlgCat.instCategory.{u,u} κ κComm)
    let e : NK ≅ ND := @Iso.trans.{u,u+1}
      ({s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ) diagramCategory NK middle ND eFirst eSecond
    (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat R S rComm sComm rSAlg N ≫
      @fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat S T sComm tComm sTAlg NS ≫
      @fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat T κ tComm κComm tκAlg NST) ≫
        @matchingIsoRingMap.{u,u,u} κ κComm {s : Finset J // s.Nonempty} jCat NK ND e =
      @fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat R κ rComm κComm rκAlg N := by
  intro jCat sSelf tSelf κSelf rSS sTT tκκ rκκ NS NST NK ND sκκ middle eFirst eSecond
      diagramCategory e
  have hfirst := @tensorCancellation_scalar.{u,u,u} S T κ sComm tComm κComm
    sTAlg tκAlg sκAlg sTκ {s : Finset J // s.Nonempty} jCat NS
  have hsecond := @tensorCancellation_scalar.{u,u,u} R S κ rComm sComm κComm
    rSAlg sκAlg rκAlg rSκ {s : Finset J // s.Nonempty} jCat N
  have hfirst' := congrArg
    (fun a => (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat
      R S rComm sComm rSAlg N) ≫ a ≫
        Functor.whiskerRight
          (@tensorCancellationIso.{u,u,u} R S κ rComm sComm κComm
            rSAlg sκAlg rκAlg rSκ {s : Finset J // s.Nonempty} jCat N).hom
          (forget₂ (CommAlgCat κ) CommRingCat)) hfirst
  have hsecond' :
      (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat
        R S rComm sComm rSAlg N) ≫
        (@fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat
          S κ sComm κComm sκAlg NS) ≫
          Functor.whiskerRight
            (@tensorCancellationIso.{u,u,u} R S κ rComm sComm κComm
              rSAlg sκAlg rκAlg rSκ {s : Finset J // s.Nonempty} jCat N).hom
            (forget₂ (CommAlgCat κ) CommRingCat) =
        @fixedScalarMap.{u,u,u} {s : Finset J // s.Nonempty} jCat R κ rComm κComm rκAlg N := by
    simpa only [Category.assoc] using hsecond
  simpa only [matchingIsoRingMap, e, eFirst, eSecond, Iso.trans_hom, Functor.whiskerRight_comp,
      Category.assoc]
    using hfirst'.trans hsecond'


private theorem polynomial_leading_of_eq {R κ J : Type u}
    [rComm : CommRing R] [κComm : CommRing κ]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ)
    (mu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (PM : ∀ j, Polynomial (M.obj (singletonIndex j)))
    (hPM : PM = @matchingScalarPolynomial.{u} R κ J rComm κComm N M mu P)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) * (delta s j hj k hk : N.obj s)) :
    ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (M.map (singletonArrow s j hj)).hom ((PM j).coeff 2) =
        (M.map (singletonArrow s k hk)).hom ((PM k).coeff 2) *
          (@matchingScalarUnits.{u} R κ J rComm κComm N M mu delta s j hj k hk : M.obj s) := by
  cases hPM
  exact @matchingScalarPolynomial_leading.{u} R κ J rComm κComm N M mu delta P hr

private theorem matching_prior_transport {R κ C J : Type u}
    [rComm : CommRing R] [κComm : CommRing κ] [cComm : CommRing C]
    {p : ℕ} [cChar : ExpChar C p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (M F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ)
    [mOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (M.map f).hom.toRingHom))]
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [mDir : ((M.op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    [fDir : ((F.op ⋙ algSpec (.of κ) ⋙ Over.forget (Spec (.of κ))) ⋙
      Scheme.forget).IsLocallyDirected]
    (mu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (nu : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (e : M ≅ F)
    (hmap : mu ≫ @matchingIsoRingMap.{u,u,u} κ κComm
      {s : Finset J // s.Nonempty} (@Preorder.smallCategory {s : Finset J // s.Nonempty}
          (@Subtype.preorder (Finset J) (@PartialOrder.toPreorder (Finset J)
          (@Finset.instPartialOrder J)) (fun s => s.Nonempty))) M F e = nu)
    (cM : Cocone (M.op ⋙ algSpec (.of κ))) (hcM : IsColimit cM)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) * (delta s j hj k hk : N.obj s))
    (PM : ∀ j, Polynomial (M.obj (singletonIndex j)))
    (hPM : PM = @matchingScalarPolynomial.{u} R κ J rComm κComm N M mu P)
    (degree : ℕ) :
    let cF := @matchingIsoCocone.{u,u,u} κ κComm {s : Finset J // s.Nonempty}
      (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
          (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s => s.Nonempty)))
          M F e cM
    let deltaM := @matchingScalarUnits.{u} R κ J rComm κComm N M mu delta
    let deltaF := @matchingScalarUnits.{u} R κ J rComm κComm N F nu delta
    let PF := @matchingScalarPolynomial.{u} R κ J rComm κComm N F nu P
    let hcoM := @matchingScalarUnits_cocycle.{u} R κ J rComm κComm N M mu delta hco
    let hnM := @matchingScalarUnits_natural.{u} R κ J rComm κComm N M mu delta hn
    let hcoF := @matchingScalarUnits_cocycle.{u} R κ J rComm κComm N F nu delta hco
    let hnF := @matchingScalarUnits_natural.{u} R κ J rComm κComm N F nu delta hn
    let hrM := @polynomial_leading_of_eq.{u} R κ J rComm κComm N M mu delta P PM hPM hr
    let hrF := @matchingScalarPolynomial_leading.{u} R κ J rComm κComm N F nu delta P hr
    let hd := @scalar_unit_comparison.{u} R κ J rComm κComm N M F mu nu e hmap delta
    let LM : cM.pt.left.Modules := @matchingModule.{u} κ J κComm M cM deltaM degree
    let LF : cM.pt.left.Modules := @matchingModule.{u} κ J κComm F cF deltaF degree
    let E : LM ≅ LF := @matchingDiagramIso.{u} κ J κComm M F mOpen fOpen mDir fDir e cM hcM
      deltaM deltaF hd degree hcoM hnM hcoF hnF
    let m : SheafOfModules.unit cM.pt.left.ringCatSheaf ⟶ LM := @coefficientMatchingSection.{u} κ J
        κComm M cM deltaM
      (fun j => (PM j).coeff 2) hrM degree
    let t : SheafOfModules.unit cM.pt.left.ringCatSheaf ⟶ LF := @coefficientMatchingSection.{u} κ J
        κComm F cF deltaF
      (fun j => (PF j).coeff 2) hrF degree
    ∀ (base : cM.pt.left ⟶ Spec (.of C))
      (Theta : frobeniusRestriction C p base
        LF ⟶
          SheafOfModules.unit cM.pt.left.ringCatSheaf)
      (_hnorm : Theta.app ⊤ (Scheme.Modules.Hom.app t ⊤ (1 : Γ(cM.pt.left, ⊤))) = (1 : Γ(cM.pt.left,
          ⊤)))
      (I : Type u) (B : I → Over cM.pt.left)
      (_hI : ∀ i (U : cM.pt.left.Opens) (r : Γ(cM.pt.left, U)), (B i).hom.app U r = 0 →
        ∀ x : Γ(LF, U),
          (B i).hom.app U (Theta.app U (r • x)) = 0),
      let Phi := @twistModuleMap.{u} C cComm p cChar cM.pt.left base
        LM LF E.hom ≫ Theta
      Phi.app ⊤ (Scheme.Modules.Hom.app m ⊤ (1 : Γ(cM.pt.left, ⊤))) = (1 : Γ(cM.pt.left, ⊤)) ∧
      ∀ i (U : cM.pt.left.Opens) (r : Γ(cM.pt.left, U)), (B i).hom.app U r = 0 →
        ∀ x : Γ(LM, U),
          (B i).hom.app U (Phi.app U (r • x)) = 0 := by
  intro cF deltaM deltaF PF hcoM hnM hcoF hnF hrM hrF hd LM LF E m t base Theta hnorm I B hI Phi
  have hcoeff : ∀ j,
      ((@matchingIsoRingMap.{u,u,u} κ κComm {s : Finset J // s.Nonempty}
        (@Preorder.smallCategory {s : Finset J // s.Nonempty} (@Subtype.preorder (Finset J)
            (@PartialOrder.toPreorder (Finset J) (@Finset.instPartialOrder J)) (fun s =>
            s.Nonempty))) M F e).app (singletonIndex j)).hom
          ((PM j).coeff 2) = (PF j).coeff 2 := by
    rw [hPM]
    exact @scalar_coefficient_comparison.{u} R κ J rComm κComm N M F mu nu e hmap P
  have hsection := @matchingDiagramIso_section.{u} κ J κComm M F mOpen fOpen mDir fDir
    e cM hcM deltaM deltaF hd degree hcoM hnM hcoF hnF
    (fun j => (PM j).coeff 2) (fun j => (PF j).coeff 2) hrM hrF hcoeff
  exact ⟨prior_map_normalized base E.hom m t hsection Theta hnorm,
    prior_map_boundary base E.hom Theta B hI⟩


private theorem polynomial_three_maps {R S T κ J : Type u}
    [rComm : CommRing R] [sComm : CommRing S] [tComm : CommRing T] [κComm : CommRing κ]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (NS : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (NT : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} T)
    (NK : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} κ)
    (mu0 : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      NS ⋙ forget₂ (CommAlgCat S) CommRingCat)
    (mu1 : NS ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      NT ⋙ forget₂ (CommAlgCat T) CommRingCat)
    (mu2 : NT ⋙ forget₂ (CommAlgCat T) CommRingCat ⟶
      NK ⋙ forget₂ (CommAlgCat κ) CommRingCat)
    (P : ∀ j, Polynomial (N.obj (singletonIndex j))) :
    @matchingScalarPolynomial.{u} T κ J tComm κComm NT NK mu2
      (@matchingScalarPolynomial.{u} S T J sComm tComm NS NT mu1
        (@matchingScalarPolynomial.{u} R S J rComm sComm N NS mu0 P)) =
      @matchingScalarPolynomial.{u} R κ J rComm κComm N NK (mu0 ≫ mu1 ≫ mu2) P := by
  funext j
  change Polynomial.map (mu2.app (singletonIndex j)).hom
    (Polynomial.map (mu1.app (singletonIndex j)).hom
      (Polynomial.map (mu0.app (singletonIndex j)).hom (P j))) =
    Polynomial.map (((mu0 ≫ mu1 ≫ mu2).app (singletonIndex j)).hom) (P j)
  rw [Polynomial.map_map, Polynomial.map_map]
  rfl

end SchubertGeometry.RetainedCharacter
