import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingInduction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The induction functional under coefficient extension

A Cartesian coefficient extension preserves the prefix functional and its
omitted-boundary kernels. The same functional also acts on the iterated
pullback through the canonical composition isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private pullSection_hom from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private twistModuleMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
open private prior_map_normalized prior_map_boundary from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordSplittingInduction

namespace SchubertGeometry.RetainedCharacter

/-- A splitting of the carried prefix gives its normalized raw functional on
any prescribed Cartesian coefficient extension, preserving all omitted
boundary kernels and the canonical iterated pullback of its section. -/
theorem retentionPrior_scalar {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    (M : PrefixModel G word) (T : Subalgebra ℤ K) (hMT : M.S ≤ T)
    (Y : Scheme.{u}) (baseT : Y ⟶ Spec (.of T)) (qT : Y ⟶ M.cG.pt.left)
    (hqT : IsPullback qT baseT M.cG.pt.hom
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMT).toRingHom)))
    (hM : PrefixSplits M) :
  let prefixL := fun degree => @matchingModule.{u} M.S M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    M.N M.cG M.delta degree
  let prefixSection := fun degree => @coefficientMatchingSection.{u} M.S M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr degree
  ∀ (κ : Type u) [κComm : CommRing κ] (_hκField : IsField κ)
    (C : Type u) [cField : Field C] [_cκAlg : Algebra C κ] (pChar : ℕ)
    [cChar : ExpChar C pChar] [_cPerfect : PerfectRing C pChar]
    (_hp : Odd pChar) (_hp' : 1 < pChar)
    (coefficientMap : Spec (@CommRingCat.of κ κComm) ⟶ Spec (.of T))
    (X : Scheme.{u}) (baseκ : X ⟶ Spec (@CommRingCat.of κ κComm))
    (x : X ⟶ Y) (_hx : IsPullback x baseκ baseT coefficientMap)
    (B : Fin word.length → Over X)
    (bD : ∀ j, (B j).left ⟶ (M.boundaries j).left)
    (_hB : ∀ j, IsPullback (B j).hom (bD j) (x ≫ qT) (M.boundaries j).hom),
    let L := prefixL ((pChar - 1) / 2)
    let sectionHom := prefixSection ((pChar - 1) / 2)
    ∃ Theta : @frobeniusRestriction.{u} C (@Field.toCommRing C cField)
        pChar cChar X (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
            ((Scheme.Modules.pullback (x ≫ qT)).obj L) ⟶
          SheafOfModules.unit X.ringCatSheaf,
      Theta.app ⊤ (@Scheme.Modules.Hom.app.{u} X
        (SheafOfModules.unit X.ringCatSheaf) ((Scheme.Modules.pullback (x ≫ qT)).obj L)
        (@pullSection.{u} X M.cG.pt.left (x ≫ qT) L sectionHom)
        ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) ∧
      (∀ j (V : X.Opens) (a : Γ(X, V)), (B j).hom.app V a = 0 →
        ∀ z : Γ((Scheme.Modules.pullback (x ≫ qT)).obj L, V),
          (B j).hom.app V (Theta.app V (a • z)) = 0) ∧
      let comparison := (@Scheme.Modules.pullbackComp.{u} X Y M.cG.pt.left x qT).app L
      let Phi := @twistModuleMap.{u} C (@Field.toCommRing C cField) pChar cChar X (baseκ ≫ Spec.map
          (CommRingCat.ofHom (algebraMap C κ)))
        ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback qT).obj L))
        ((Scheme.Modules.pullback (x ≫ qT)).obj L) comparison.hom ≫ Theta
      Phi.app ⊤ (@Scheme.Modules.Hom.app.{u} X
        (SheafOfModules.unit X.ringCatSheaf)
        ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback qT).obj L))
        (@pullSection.{u} X Y x ((Scheme.Modules.pullback qT).obj L)
          (@pullSection.{u} Y M.cG.pt.left qT L sectionHom))
        ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) ∧
      ∀ j (V : X.Opens) (a : Γ(X, V)), (B j).hom.app V a = 0 →
        ∀ z : Γ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback qT).obj L), V),
          (B j).hom.app V (Phi.app V (a • z)) = 0 := by
  intro prefixL prefixSection κ κComm hκField C cField cκAlg pChar cChar cPerfect
    hp hp' coefficientMap X baseκ x hx B bD hB L sectionHom
  let scalarMap : Spec (.of T) ⟶ Spec (.of M.S) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hMT).toRingHom)
  have hxPrefix : IsPullback (x ≫ qT) baseκ M.cG.pt.hom
      (coefficientMap ≫ scalarMap) := hx.paste_horiz hqT
  have hPrefix :=
    @hM κ κComm hκField C cField cκAlg pChar cChar cPerfect hp hp'
      (coefficientMap ≫ scalarMap) X baseκ (x ≫ qT) hxPrefix B bD hB
  obtain ⟨Theta, hnormal, hboundary⟩ := hPrefix
  refine ⟨Theta, hnormal, hboundary, ?_⟩
  intro comparison
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let .letE _ _ value body _ := (← goal.getType).consumeMData
      | throwError "expected the outer Phi let"
    let next ← goal.replaceTargetDefEq (body.instantiate1 value)
    Lean.Elab.Tactic.replaceMainGoal [next]
  have hsection : @pullSection.{u} X Y x ((Scheme.Modules.pullback qT).obj L)
      (@pullSection.{u} Y M.cG.pt.left qT L sectionHom) ≫ comparison.hom =
        @pullSection.{u} X M.cG.pt.left (x ≫ qT) L sectionHom :=
    @pullSection_hom.{u} X Y M.cG.pt.left x qT L sectionHom
  have hNormalized :=
    @prior_map_normalized.{u} C (@Field.toCommRing C cField) pChar cChar X (baseκ ≫ Spec.map
        (CommRingCat.ofHom (algebraMap C κ)))
      ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback qT).obj L))
      ((Scheme.Modules.pullback (x ≫ qT)).obj L) comparison.hom
      (@pullSection.{u} X Y x ((Scheme.Modules.pullback qT).obj L)
        (@pullSection.{u} Y M.cG.pt.left qT L sectionHom))
      (@pullSection.{u} X M.cG.pt.left (x ≫ qT) L sectionHom) hsection Theta hnormal
  have hBoundary :=
    @prior_map_boundary.{u, 0} C (@Field.toCommRing C cField) pChar cChar X (baseκ ≫ Spec.map
        (CommRingCat.ofHom (algebraMap C κ)))
      ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback qT).obj L))
      ((Scheme.Modules.pullback (x ≫ qT)).obj L) comparison.hom Theta
      (Fin word.length) B hboundary
  exact ⟨hNormalized, hBoundary⟩

private theorem pullSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L N : Y.Modules} (a : L ⟶ N)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ N) (hs : s ≫ a = t) :
    @pullSection.{u} X Y f L s ≫ (Scheme.Modules.pullback f).map a =
      @pullSection.{u} X Y f N t := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Scheme.Modules.pullbackObjUnitIso f).inv ≫ z)
      ((Scheme.Modules.pullback f).map_comp s a).symm).trans
        (congrArg (fun z => (Scheme.Modules.pullbackObjUnitIso f).inv ≫
          (Scheme.Modules.pullback f).map z) hs))

/-- A coefficient-stage matching-line isomorphism transports a normalized
functional on an iterated pullback, including every specified kernel. -/
theorem PrefixScalarModel.fibre_functional {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} (h : PrefixScalarModel M)
    (C : Type u) [cComm : CommRing C] (p : ℕ) [cChar : ExpChar C p]
    (X : Scheme.{u}) (baseC : X ⟶ Spec (.of C)) (x : X ⟶ h.cT.pt.left) :
  let LN := @matchingModule.{u} M.S M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    M.N M.cG M.delta ((p - 1) / 2)
  let sN := @coefficientMatchingSection.{u} M.S M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr ((p - 1) / 2)
  let LF := @matchingModule.{u} h.prefix.S h.prefix.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.prefix.S)
    h.prefix.N h.prefix.cG h.prefix.delta ((p - 1) / 2)
  let sF := @coefficientMatchingSection.{u} h.prefix.S h.prefix.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.prefix.S)
    h.prefix.N h.prefix.cG h.prefix.delta
    (fun j => (h.prefix.P (singletonIndex j)).coeff 2) h.prefix.hr ((p - 1) / 2)
  ∀ (I : Type v) (B : I → Over X)
    (Theta : @frobeniusRestriction.{u} C cComm p cChar X baseC
      ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback h.qT).obj LN)) ⟶
        SheafOfModules.unit X.ringCatSheaf)
    (_hnormal : Theta.app ⊤ (@Scheme.Modules.Hom.app.{u} X
      (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback h.qT).obj LN))
      (@pullSection.{u} X h.cT.pt.left x ((Scheme.Modules.pullback h.qT).obj LN)
        (@pullSection.{u} h.cT.pt.left M.cG.pt.left h.qT LN sN))
      ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)))
    (_hboundary : ∀ j (V : X.Opens) (a : Γ(X, V)), (B j).hom.app V a = 0 →
      ∀ z : Γ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback h.qT).obj LN), V),
        (B j).hom.app V (Theta.app V (a • z)) = 0),
    ∃ Phi : @frobeniusRestriction.{u} C cComm p cChar X baseC
        ((Scheme.Modules.pullback x).obj LF) ⟶ SheafOfModules.unit X.ringCatSheaf,
      Phi.app ⊤ (@Scheme.Modules.Hom.app.{u} X
        (SheafOfModules.unit X.ringCatSheaf) ((Scheme.Modules.pullback x).obj LF)
        (@pullSection.{u} X h.cT.pt.left x LF sF) ⊤ (1 : Γ(X, ⊤))) =
          (1 : Γ(X, ⊤)) ∧
      ∀ j (V : X.Opens) (a : Γ(X, V)), (B j).hom.app V a = 0 →
        ∀ z : Γ((Scheme.Modules.pullback x).obj LF, V),
          (B j).hom.app V (Phi.app V (a • z)) = 0 := by
  intro LN sN LF sF I B Theta hnormal hboundary
  let vT := @fixedScalarMap.{u,u,u}
    {s : Finset M.J // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset M.J // s.Nonempty}))
    M.S h.T
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
    (@RingHom.toAlgebra M.S h.T
      (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
      (@Subalgebra.toCommSemiring ℤ K Int.instCommSemiring
        (@Semifield.toCommSemiring K (@Field.toSemifield K kField))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
      (@Subalgebra.inclusion ℤ K Int.instCommSemiring
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K kField)))
        (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField)))
        M.S h.T h.hMT).toRingHom) M.N
  have hLeg : ∀ s, Spec.map (vT.app s) ≫ (M.cG.ι.app (op s)).left =
      (h.prefix.cG.ι.app (op s)).left ≫ h.qT := fun s => (h.hLeg s).symm
  have hd : ∀ s j hj k hk, (vT.app s).hom (M.delta s j hj k hk : M.N.obj s) =
      (h.prefix.delta s j hj k hk : h.prefix.N.obj s) := fun _ _ _ _ _ => rfl
  let E := @matchingPullbackIso.{u} M.S h.T M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
    M.N h.prefix.N (@M.nOpen) (@h.prefix.nOpen) M.nDir h.prefix.nDir
    M.cG M.hcG h.prefix.cG h.prefix.hcG vT h.qT hLeg
    M.delta h.prefix.delta hd ((p - 1) / 2) M.hco M.hn h.prefix.hco h.prefix.hn
  have hSection := @matchingPullbackIso_section.{u} M.S h.T M.J
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) h.T)
    M.N h.prefix.N (@M.nOpen) (@h.prefix.nOpen) M.nDir h.prefix.nDir
    M.cG M.hcG h.prefix.cG h.prefix.hcG vT h.qT hLeg
    M.delta h.prefix.delta hd ((p - 1) / 2) M.hco M.hn h.prefix.hco h.prefix.hn
    (fun j => (M.P (singletonIndex j)).coeff 2)
    (fun j => (h.prefix.P (singletonIndex j)).coeff 2) M.hr h.prefix.hr
    (fun j => (h.hCoefficientImage j).symm)
  have hInverse : sF ≫ E.inv =
      @pullSection.{u} h.cT.pt.left M.cG.pt.left h.qT
        (@matchingModule.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta ((p - 1) / 2))
        (@coefficientMatchingSection.{u} M.S M.J
          (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
            (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
          M.N M.cG M.delta (fun j => (M.P (singletonIndex j)).coeff 2) M.hr
          ((p - 1) / 2)) :=
    (Iso.comp_inv_eq E).2 hSection.symm
  have hPull := @pullSection_map.{u} X h.cT.pt.left x _ _ E.inv
    sF _ hInverse
  have hNormalized := @prior_map_normalized.{u} C cComm
    p cChar X baseC
    _ _ ((Scheme.Modules.pullback x).map E.inv)
    (@pullSection.{u} X h.cT.pt.left x LF sF) _ hPull Theta hnormal
  have hBoundary := @prior_map_boundary.{u, v} C cComm
    p cChar X baseC
    _ _ ((Scheme.Modules.pullback x).map E.inv) Theta I B hboundary
  exact ⟨_, hNormalized, hBoundary⟩

/-- Extending the coefficient stage of a prefix preserves its normalized
functional and every omitted-boundary kernel on all field fibres. -/
theorem PrefixScalarModel.splits {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {G : ReductiveGroupData K}
    {word : List (@simpleRootIndex.{u} K kField kClosed kZero G)}
    {M : PrefixModel G word} (h : PrefixScalarModel M)
    (hM : PrefixSplits M) : PrefixSplits h.prefix := by
  intro κ κComm hκField C cField cκAlg pChar cChar cPerfect hp hp'
    coefficientMap X baseκ x hx B bD hB L sectionHom
  have hEarlier : ∀ j, IsPullback (B j).hom (bD j ≫ h.qB j)
      (x ≫ h.qT) (M.boundaries j).hom := fun j => (hB j).paste_vert (h.hqB j)
  obtain ⟨Theta, _, _, hnormal, hboundary⟩ :=
    @retentionPrior_scalar.{u} K kField kClosed kZero G word M
      h.T h.hMT h.cT.pt.left h.cT.pt.hom h.qT h.hqT hM
      κ κComm hκField C cField cκAlg pChar cChar cPerfect hp hp'
      coefficientMap X baseκ x hx B (fun j => bD j ≫ h.qB j) hEarlier
  let ThetaT := @twistModuleMap.{u} C (@Field.toCommRing C cField)
    pChar cChar X (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ)))
    _ _ ((@Scheme.Modules.pullbackComp.{u} X h.cT.pt.left M.cG.pt.left x h.qT).app
      (@matchingModule.{u} M.S M.J
        (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
          (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) M.S)
        M.N M.cG M.delta ((pChar - 1) / 2))).hom ≫ Theta
  exact @PrefixScalarModel.fibre_functional.{u,0} K kField kClosed kZero G word M h
    C (@Field.toCommRing C cField) pChar cChar X
    (baseκ ≫ Spec.map (CommRingCat.ofHom (algebraMap C κ))) x
    (Fin word.length) B ThetaT hnormal hboundary

end SchubertGeometry.RetainedCharacter
