import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialFamilies
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFamilySections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordFramePolynomials
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Arithmetic word sections on the retained polynomial cover

The preceding word polynomial is carried along its coefficient diagram.
Its complete frame comparison determines the chart values of the next word
section, in every degree on one scalar model and one polynomial cover.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.OperatorSheaf
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private wordPolynomialData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private fieldMap oldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private framePolynomial from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendSections
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private polynomialFamilyData modelPolynomialFamilyData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialFamilies

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The singleton polynomial on the preceding coefficient diagram, after
the prescribed change of coefficients and restriction to an intersection. -/
def arithmeticNodePolynomial {R S J : Type u} [CommRing R] [CommRing S]
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (A : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (tau : M ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      A ⋙ forget₂ (CommAlgCat S) CommRingCat)
    (P : ∀ j, Polynomial (M.obj (singletonIndex j)))
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    Polynomial (A.obj s) :=
  Polynomial.map (A.map (singletonArrow s j hj)).hom.toRingHom
    (matchingScalarPolynomial M A tau P j)

/-- The full word coefficient comparison commutes with the retained scalar
map before it is evaluated in an append frame. -/
theorem wordArithmeticPolynomial_chart {K R S J : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] [CommRing R] [CommRing S] [Algebra S K]
    (G : ReductiveGroupData K) (i : G.rootBase.support)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (v : M ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (P : ∀ s, Polynomial (M.obj s)) (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (hpoly : wordPolynomialData G F point a i M v P)
    (V : J → Over (Spec (.of K)))
    (b : ∀ j, V j ⟶ (oppositeUnipotentVariety G).toOver)
    (p : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V j)
    (hsingle : ∀ j, a j = p (singletonIndex j) j (Finset.mem_singleton_self j) ≫ b j)
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (A : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (tau : M ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      A ⋙ forget₂ (CommAlgCat S) CommRingCat)
    (e : ∀ s, K ⊗[S] A.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s x, e s ((1 : K) ⊗ₜ[S] (tau.app s).hom x) = (v.app s).hom x) :
    ∀ s j hj, Polynomial.map
      ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
      (arithmeticNodePolynomial M A tau (fun j => P (singletonIndex j)) s j hj) =
      framePolynomial G i (F.obj s) (p s j hj ≫ b j) (point j) := by
  have hframe := wordFramePolynomial_chart G i M F v P point a hpoly V b p hsingle hpn
  intro s j hj
  let f := singletonArrow s j hj
  let w : A.obj s →+* F.obj s :=
    (e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have hnat : (A.map f).hom.toRingHom.comp (tau.app (singletonIndex j)).hom =
      (tau.app s).hom.comp (M.map f).hom.toRingHom :=
    congrArg (fun h => h.hom) (tau.naturality f).symm
  have heq : w.comp (tau.app s).hom = (v.app s).hom :=
    RingHom.ext (he s)
  have hnatP : Polynomial.map (A.map f).hom.toRingHom
        (Polynomial.map (tau.app (singletonIndex j)).hom (P (singletonIndex j))) =
      Polynomial.map (tau.app s).hom
        (Polynomial.map (M.map f).hom.toRingHom (P (singletonIndex j))) := by
    simpa only [Polynomial.map_map] using
      congrArg (fun g => Polynomial.map g (P (singletonIndex j))) hnat
  change Polynomial.map w
    (Polynomial.map (A.map f).hom.toRingHom
      (Polynomial.map (tau.app (singletonIndex j)).hom (P (singletonIndex j)))) = _
  calc
    _ = Polynomial.map w (Polynomial.map (tau.app s).hom
        (Polynomial.map (M.map f).hom.toRingHom (P (singletonIndex j)))) := by
      exact congrArg (Polynomial.map w) hnatP
    _ = Polynomial.map (v.app s).hom
        (Polynomial.map (M.map f).hom.toRingHom (P (singletonIndex j))) := by
      rw [Polynomial.map_map, heq]
    _ = _ := hframe s j hj


/-- Polynomial section coordinates in every degree on one scalar cover. -/
def arithmeticPolynomialSectionData {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {Y YT YK Z : Scheme.{u}} (baseT : YT ⟶ Spec (.of T))
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y) (hbase : n ≫ q = m)
    (W V : Y.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → Y.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z)))))
    (sectionHom : ∀ d, unitModule Y ⟶ L d)
    (P : ∀ z, Polynomial (A z)) (eps : V.I₀ → ULift.{u} (Fin 2)) : Prop :=
  let WT := W.pullback₂ q
  Finite WT.I₀ ∧
    ∃ (VT : YT.OpenCover.{u}) (_hfinite : Finite VT.I₀) (_haffine : ∀ z, IsAffine (VT.X z))
      (index : VT.I₀ ≃ V.I₀)
      (eVT : ∀ z, VT.X z ≅ Spec (.of (Polynomial (T ⊗[S] A (index z)))))
      (_hcart : ∀ z, IsPullback ((eVT z).hom ≫ oldMap) (VT.f z)
        ((eV (index z)).inv ≫ V.f (index z)) q)
      (_hstruct : ∀ z, VT.f z ≫ baseT = (eVT z).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A (index z))))))
      (_hold : ∀ z, VT.f z ≫ q = (eVT z).hom ≫ oldMap ≫
        (eV (index z)).inv ≫ V.f (index z))
      (_hcoord : ∀ z, IsPullback (fieldMap (e₀ (index z))) (jK (index z))
        ((eVT z).inv ≫ VT.f z) n)
      (hactual : ∀ z, IsPullback (fieldMap (e₀ (index z)) ≫ (eVT z).inv)
        (jK (index z)) (VT.f z) n),
      (∀ z, jK (index z) ≫ n = fieldMap (e₀ (index z)) ≫ (eVT z).inv ≫ VT.f z) ∧
      ∀ d, scalarPolynomialSectionFamily n r ((Scheme.Modules.pullback q).obj (L d)) (LK d)
        (((pullbackComp n q).app (L d) ≪≫ (pullbackCongr hbase).app (L d)) ≪≫ EL d)
        WT VT index (fun z => Spec (.of (Polynomial (B z)))) jK c hc (Epoly d)
        (fun z => fieldMap (e₀ (index z)) ≫ (eVT z).inv) (fun z => (hactual z).w)
        (pullSection q (L d) (sectionHom d))
        (fun z => (eVT z).hom.appTop
          ((Scheme.ΓSpecIso (.of (Polynomial (T ⊗[S] A (index z))))).inv
            (sectionChartPolynomial (2 * d)
              ((Polynomial.map (Algebra.TensorProduct.includeRight :
                A (index z) →ₐ[S] T ⊗[S] A (index z)).toRingHom (P (index z))) ^ d)
              (eps (index z)).down)))

/-- A scalar word model and its fixed all-degree polynomial section cover. -/
def arithmeticWordSectionModels {J : Type v} [Category.{w} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S) (cN : Cocone (N.op ⋙ algSpec (.of S)))
    {YK Z : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (W V : cN.pt.left.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → cN.pt.left.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z)))))
    (sectionHom : ∀ d, unitModule cN.pt.left ⟶ L d)
    (P : ∀ z, Polynomial (A z)) (eps : V.I₀ → ULift.{u} (Fin 2)) : Prop :=
  let NT := fixedFibreDiagram (R := T) (M := T) N
  (∀ {i j : Jᵒᵖ} (f : i ⟶ j),
    IsOpenImmersion (((NT.op ⋙ algSpec (.of T)).map f).left)) ∧
    ((((NT.op ⋙ algSpec (.of T)) ⋙ Over.forget (Spec (.of T))) ⋙
      Scheme.forget).IsLocallyDirected) ∧
    ∃ (cT : Cocone (NT.op ⋙ algSpec (.of T))) (q : cT.pt.left ⟶ cN.pt.left)
      (n : YK ⟶ cT.pt.left) (_hcT : IsColimit cT)
      (_hq : IsPullback q cT.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap S T))))
      (_hn : IsPullback n baseK cT.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap T K))))
      (hbase : n ≫ q = m),
      (n ≫ cT.pt.hom = baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
      (∀ i, (cT.ι.app i).left ≫ q = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj i.unop →ₐ[S]
          T ⊗[S] N.obj i.unop).toRingHom) ≫ (cN.ι.app i).left) ∧
      Smooth cT.pt.hom ∧ cT.pt.left.IsSeparated ∧
      arithmeticPolynomialSectionData cT.pt.hom q n m hbase W V A B eV e₀ jK r c hc
        L LK EL Epoly sectionHom P eps


section Word
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
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
    (S : Subalgebra ℤ K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

variable [Finite J] [cN.pt.left.IsSeparated] [Smooth cN.pt.hom]
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (PN : ∀ s, Polynomial (N.obj s))
    (hPN : ∀ j, (v.app (singletonIndex j)).hom ((PN (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)
    (hK : IsPullback qN cF.pt.hom cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (V : cN.pt.left.OpenCover.{u}) [Finite V.I₀] [∀ z, IsAffine (V.X z)]

variable {R₀ J₀ : Type u} [CommRing R₀]
    (M : {s : Finset J₀ // s.Nonempty} ⥤ CommAlgCat.{u} R₀)
    (F₀ : {s : Finset J₀ // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (v₀ : M ⋙ forget₂ (CommAlgCat R₀) CommRingCat ⟶
      F₀ ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (P₀ : ∀ s, Polynomial (M.obj s))
    (point₀ : J₀ → G.points)
    (a₀ : ∀ j, (algSpec (.of K)).obj (op (F₀.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (hpoly₀ : wordPolynomialData G F₀ point₀ a₀ i M v₀ P₀)
    (V₀ : J₀ → Over (Spec (.of K)))
    (b₀ : ∀ j, V₀ j ⟶ (oppositeUnipotentVariety G).toOver)
    (p₀ : ∀ (s : {s : Finset J₀ // s.Nonempty}) (j : J₀) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F₀.obj s)) ⟶ V₀ j)
    (hsingle : ∀ j, a₀ j = p₀ (singletonIndex j) j (Finset.mem_singleton_self j) ≫ b₀ j)
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F₀.map f).op ≫ p₀ s j hj = p₀ t j ((leOfHom f) hj))
    (A₀ : {s : Finset J₀ // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (tau : M ⋙ forget₂ (CommAlgCat R₀) CommRingCat ⟶
      A₀ ⋙ forget₂ (CommAlgCat S) CommRingCat)
    (e₀ : ∀ s, K ⊗[S] A₀.obj s ≃ₐ[K] F₀.obj s)
    (he₀ : ∀ s x, e₀ s ((1 : K) ⊗ₜ[S] (tau.app s).hom x) = (v₀.app s).hom x)
    (indexNode : V.I₀ → {s : Finset J₀ // s.Nonempty})
    (sel : ∀ s : {s : Finset J₀ // s.Nonempty}, {j // j ∈ s.val})
    (c₀ : ∀ j, V₀ j ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend₀ : ∀ j, (c₀ j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b₀ j ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (point₀ j))
    (eps : V.I₀ → ULift.{u} (Fin 2))
    (π : ∀ z, Spec (.of (Polynomial (F₀.obj (indexNode z)))) ⟶ V.X z)
    (jK : ∀ z, Spec (.of (Polynomial (F₀.obj (indexNode z)))) ⟶ cF.pt.left)

variable
    (hV : ∀ z, IsPullback (π z) (jK z) (V.f z) qN)
    (hword : ∀ z, jK z ≫ q = projectiveLinePolynomialChart (F₀.obj (indexNode z)) (eps z) ≫
      projectiveAppendChart G i (F₀.obj (indexNode z)) (p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) (c₀ (Subtype.val (sel (indexNode z)))))
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A₀.obj (indexNode z)))))
    (hVbase : ∀ z, ((eV z).inv ≫ V.f z) ≫ cN.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A₀.obj (indexNode z))))))
    (hπ : ∀ z, π z = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ (indexNode z)).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ (eV z).inv)
    (hjKb : ∀ z, jK z ≫ cF.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (F₀.obj (indexNode z))))))
    (eNodes : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (heNodes : ∀ s x, eNodes s ((1 : K) ⊗ₜ[S] x) = (v.app s).hom x)
    (hqBase : q ≫ bsdhToSpec G (word ++ [i]) = cF.pt.hom)
    (hdata : commonMatchingCoframeData G word i S N cN hcN deltaN hcoN hnN
      cF.pt.hom qN hK q
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN 1)
      V
      (fun z : V.I₀ => V₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => point₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => b₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => c₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => hend₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => F₀.obj (indexNode z))
      (fun z : V.I₀ => p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) eps π jK T hST)

include hV hword hVbase hπ hjKb hpoly₀ hsingle hpn he₀ hv hPN
  hK eNodes heNodes hqBase hdata in
/-- The preceding polynomial producer and the canonical next-word section
give all section coordinates on one retained matching model and cover.
The two polynomial families keep their respective coefficient diagrams. -/
theorem exists_word_arithmetic_sections :
    let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    arithmeticWordSectionModels (T := T) N cN cF.pt.hom qN
      (matchingSingletonCover N cN hcN) V
      (fun z : V.I₀ => A₀.obj (indexNode z))
      (fun z : V.I₀ => F₀.obj (indexNode z)) eV (fun z : V.I₀ => e₀ (indexNode z)) jK q
      (fun z => projectiveLinePolynomialChart (F₀.obj (indexNode z)) (eps z) ≫
        projectiveAppendChart G i (F₀.obj (indexNode z)) (p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) (c₀ (Subtype.val (sel (indexNode z))))) hword
      (fun d => matchingModule N cN deltaN d)
      (fun d => CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ d) (word ++ [i]))
      (fun d => retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN d)
      (fun d z => appendPolynomialFrame G word i (V₀ (Subtype.val (sel (indexNode z)))) (point₀ (Subtype.val (sel (indexNode z)))) (b₀ (Subtype.val (sel (indexNode z)))) (c₀ (Subtype.val (sel (indexNode z)))) (hend₀ (Subtype.val (sel (indexNode z))))
        (F₀.obj (indexNode z)) (p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) d (eps z))
      (fun d => retainedWordSection G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v hv deltaN hd PN hPN cN d)
      (fun z : V.I₀ => arithmeticNodePolynomial M A₀ tau
  (fun j => P₀ (singletonIndex j)) (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) eps := by
  classical
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  have hP := wordArithmeticPolynomial_chart G i M F₀ v₀ P₀ point₀ a₀ hpoly₀
    V₀ b₀ p₀ hsingle hpn A₀ tau e₀ he₀
  have hmodel := exists_matching_polynomial_families G F cF hcF word i q point a ha beta
    hgroup hco hn S N v deltaN hd cN hcN qN hqN hcoN hnN hK
    V
      (fun z : V.I₀ => V₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => point₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => b₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => c₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => hend₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => F₀.obj (indexNode z))
      (fun z : V.I₀ => p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) eps π jK hV hword T hST (fun z : V.I₀ => A₀.obj (indexNode z)) eV hVbase (fun z : V.I₀ => e₀ (indexNode z)) hπ hjKb
    eNodes heNodes hqBase hdata
  obtain ⟨hopen, hdir, cT, qT, n, hcT, hqT, hnativePB, hbase, hnbase, hlegs,
    hsmooth, hsep, hpoly⟩ := hmodel
  let : Smooth cT.pt.hom := hsmooth
  obtain ⟨hfiniteW, VT, hfiniteV, haffine, index, eVT, hcart, hstruct,
    hold, hcoord, hactual, hnative, hfamily⟩ := hpoly
  let : ∀ z, IsAffine (VT.X z) := haffine
  have hsections := matchingFamily_sections G F cF hcF word i q point a ha beta hgroup hco hn
    N v deltaN hd cN hcN qN hqN hcoN hnN hv PN hPN
    (show Function.Injective (algebraMap T K) from Subtype.val_injective)
    cT.pt.hom qT n hbase hnativePB ((matchingSingletonCover N cN hcN).pullback₂ qT)
    VT index (fun z : V.I₀ => V₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => point₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => b₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => c₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => hend₀ (Subtype.val (sel (indexNode z))))
      (fun z : V.I₀ => A₀.obj (indexNode z))
      (fun z : V.I₀ => F₀.obj (indexNode z))
      (fun z : V.I₀ => p₀ (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) eps (fun z : V.I₀ => e₀ (indexNode z)) eVT jK hword hactual (fun z : V.I₀ => arithmeticNodePolynomial M A₀ tau
  (fun j => P₀ (singletonIndex j)) (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z))))
    (fun z => hP (indexNode z) (Subtype.val (sel (indexNode z))) (Subtype.property (sel (indexNode z)))) hfamily
  exact ⟨hopen, hdir, cT, qT, n, hcT, hqT, hnativePB, hbase, hnbase, hlegs,
    hsmooth, hsep, hfiniteW, VT, hfiniteV, haffine, index, eVT, hcart, hstruct,
    hold, hcoord, hactual, hnative, hsections⟩

end Word

end SchubertGeometry.RetainedCharacter
