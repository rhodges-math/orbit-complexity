import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.SpecializedWordSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarNodeSections
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarData
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Word-section coordinates on prescribed scalar nodes

The polynomial cover is chosen once, then its inherited node index identifies
both charts of every projective node. The section equations are obtained from
the arithmetic section family on the same model.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.OperatorSheaf FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private nodePolynomial from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private scalar_natural_apply from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarData
open private scalar_node coefficient nodeBase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarProjectiveNodes
open private AppendChartData AppendChartData.I AppendChartData.sel AppendChartData.N
  AppendChartContext AppendChartStage AppendChartStage.q AppendChartStage.V AppendChartStage.finite
  AppendChartStage.index AppendChartStage.eV AppendChartStage.hold AppendChartStage.hbase
  AppendChartContext.D AppendChartContext.eP
  AppendChartContext.cD AppendChartContext.hOpen AppendChartContext.hCover AppendChartContext.base
      from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
open private chartMap chartCoframe fieldCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.SpecializedWordSections

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A (ULift.{u} (Fin 2))

private def scalarWordPolynomial {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {J : Type u} (A : J → CommAlgCat.{u} R)
    (P : ∀ s, Polynomial (A s)) (n : ℕ) (s : J) : Polynomial (K ⊗[R] A s) :=
  (Polynomial.map (Algebra.TensorProduct.includeRight :
    A s →ₐ[R] K ⊗[R] A s).toRingHom (P s)) ^ n

private def singletonPolynomial {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (Q : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    (s : {s : Finset J // s.Nonempty}) : Polynomial (N.obj s) :=
  Polynomial.map (N.map (singletonArrow s (sel s).1 (sel s).2)).hom.toRingHom
    (Q (sel s).1)

private theorem scalarWordPolynomial_node {R K J : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (Q : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val}) :
    scalarWordPolynomial (K := K) N.obj (singletonPolynomial N Q sel) =
      fun n s => nodePolynomial (fixedFibreDiagram (R := K) (M := K) N)
        (matchingScalarPolynomial N (fixedFibreDiagram (R := K) (M := K) N)
          (fixedScalarMap R K N) Q) n sel s := by
  let M := fixedFibreDiagram (R := K) (M := K) N
  let μ := fixedScalarMap R K N
  funext n s
  let f := singletonArrow s (sel s).1 (sel s).2
  have hmaps : (μ.app s).hom.comp (N.map f).hom.toRingHom =
      (M.map f).hom.toRingHom.comp (μ.app (singletonIndex (sel s).1)).hom := by
    ext a
    exact scalar_natural_apply N M μ _ _ f a
  change (Polynomial.map (μ.app s).hom
      (Polynomial.map (N.map f).hom.toRingHom (Q (sel s).1))) ^ n =
    (Polynomial.map (M.map f).hom.toRingHom
      (Polynomial.map (μ.app (singletonIndex (sel s).1)).hom (Q (sel s).1))) ^ n
  rw [Polynomial.map_map, Polynomial.map_map, hmaps]

/-- One polynomial cover and one family of scalar projective nodes carry the
section coordinates in every degree and in the half-character degree. -/
def scalarWordCoordinateData {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {J : Type u} (A : J → CommAlgCat.{u} R)
    {X Y : Scheme.{u}} (baseK : Y ⟶ Spec (.of K)) (q : Y ⟶ X)
    (old : ∀ s, line (A s) ⟶ X)
    (L : ℕ → X.Modules) (sectionHom : ∀ n, unitModule X ⟶ L n)
    (P : ∀ (_n : ℕ) (s : J), Polynomial (K ⊗[R] A s)) : Prop :=
  ∃ Knode : ∀ s, line (K ⊗[R] A s) ⟶ Y,
    (∀ s, Knode s ≫ q = coefficient R K (A s) ≫ old s) ∧
    (∀ s, Knode s ≫ baseK = nodeBase R K (A s)) ∧
    (∀ s, IsPullback (coefficient R K (A s)) (Knode s) (old s) q) ∧
    (∀ s, IsOpenImmersion (Knode s)) ∧
    ∃ (V : Y.OpenCover.{u}) (_hfinite : Finite V.I₀)
      (_haffine : ∀ v, IsAffine (V.X v))
      (index : V.I₀ ≃ J × ULift.{u} (Fin 2))
      (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (K ⊗[R] A (index v).1)))),
      (∀ v, V.f v ≫ q = (eV v).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
          (Algebra.TensorProduct.includeRight :
            A (index v).1 →ₐ[R] K ⊗[R] A (index v).1).toRingHom)) ≫
        projectiveLinePolynomialChart (A (index v).1) (index v).2 ≫ old (index v).1) ∧
      (∀ v, V.f v ≫ baseK = (eV v).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (K ⊗[R] A (index v).1))))) ∧
      (∀ v, projectiveLinePolynomialChart (K ⊗[R] A (index v).1) (index v).2 ≫
        Knode (index v).1 = (eV v).inv ≫ V.f v) ∧
      let coordinate := fun n degree =>
        ∃ E : ∀ s (j : ULift.{u} (Fin 2)),
          (Scheme.Modules.pullback
            (projectiveLinePolynomialChart (K ⊗[R] A s) j ≫ Knode s)).obj
              ((Scheme.Modules.pullback q).obj (L n)) ≅
            unitModule (Spec (.of (Polynomial (K ⊗[R] A s)))),
          ∀ s j, sectionValue
            (projectiveLinePolynomialChart (K ⊗[R] A s) j ≫ Knode s)
            ((Scheme.Modules.pullback q).obj (L n)) (pullSection q (L n) (sectionHom n))
            (E s j).hom ((Scheme.ΓSpecIso (.of (Polynomial (K ⊗[R] A s)))).inv
              (sectionChartPolynomial degree
                (P n s) j.down))
      (∀ n, coordinate n (2 * n)) ∧
        ∀ prime, Odd prime → coordinate ((prime - 1) / 2) (prime - 1)

section Generic

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {J : Type u} (A : J → CommAlgCat.{u} R)
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of R))
    (baseK : Y ⟶ Spec (.of K)) (q : Y ⟶ X)
    (hq : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (old : ∀ s, line (A s) ⟶ X)
    (hopen : ∀ s, IsOpenImmersion (old s))
    (hOldBase : ∀ s, old s ≫ base = projectiveToSpec (A s) (ULift.{u} (Fin 2)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (A s))))
    (U : X.OpenCover.{u}) [Finite U.I₀]
    (indexU : U.I₀ ≃ J × ULift.{u} (Fin 2))
    (eU : ∀ i, U.X i ≅ Spec (.of (Polynomial (A (indexU i).1))))
    (hU : ∀ i, U.f i ≫ base = (eU i).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (A (indexU i).1)))))
    (hchart : ∀ i, (eU i).inv ≫ U.f i =
      projectiveLinePolynomialChart (A (indexU i).1) (indexU i).2 ≫ old (indexU i).1)
    (L : ℕ → X.Modules) (sectionHom : ∀ n, unitModule X ⟶ L n)
    (P : ∀ s, Polynomial (A s))

omit [Finite U.I₀] in
include hq hopen hOldBase hchart in
private theorem node_coordinates
    (F : ∀ n i, (Scheme.Modules.pullback (U.f i)).obj (L n) ≅ unitModule (U.X i))
    (hfield : specializedPolynomialSectionData baseK q U
      (fun i => A (indexU i).1) eU L sectionHom F
      (fun i => P (indexU i).1) (fun i => (indexU i).2)) :
    scalarWordCoordinateData A baseK q old L sectionHom (scalarWordPolynomial A P) := by
  classical
  choose Knode hOld hBase hCart hOpen using fun s =>
    @scalar_node R K (A s) _ _ _ _ _ X Y base baseK q hq (old s)
      (hopen s) (hOldBase s)
  obtain ⟨V, hfinite, haffine, index, eV, hcart, hbase, hold, hspec, hspecBase,
    hcoordinates⟩ := hfield
  let indexV := index.trans indexU
  have holdV (v : V.I₀) : V.f v ≫ q = (eV v).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight :
          A (indexV v).1 →ₐ[R] K ⊗[R] A (indexV v).1).toRingHom)) ≫
      projectiveLinePolynomialChart (A (indexV v).1) (indexV v).2 ≫ old (indexV v).1 := by
    exact (hold v).trans (congrArg (fun a => (eV v).hom ≫ _ ≫ a) (hchart (index v)))
  have hnode (v : V.I₀) :
      projectiveLinePolynomialChart (K ⊗[R] A (indexV v).1) (indexV v).2 ≫
        Knode (indexV v).1 = (eV v).inv ≫ V.f v :=
    scalarCover_node_chart A base baseK q hq old Knode hOld hBase V indexV eV holdV hbase v
  refine ⟨Knode, hOld, hBase, hCart, hOpen, V, hfinite, haffine,
    indexV, eV, holdV, hbase, hnode, ?_⟩
  intro coordinate
  have transfer (n degree : ℕ)
      (hc : ∀ v, sectionValue (chartMap (eV v) (V.f v))
        ((Scheme.Modules.pullback q).obj (L n)) (pullSection q (L n) (sectionHom n))
        (fieldCoframe q (chartMap (eV v) (V.f v))
          (chartMap (eU (index v)) (U.f (index v))) (hspec v) (L n)
          (chartCoframe (eU (index v)) (U.f (index v)) (L n) (F n (index v)))).hom
        ((Scheme.ΓSpecIso (.of (Polynomial (K ⊗[R] A (indexV v).1)))).inv
          (sectionChartPolynomial degree
            ((Polynomial.map (Algebra.TensorProduct.includeRight :
              A (indexV v).1 →ₐ[R] K ⊗[R] A (indexV v).1).toRingHom
                (P (indexV v).1)) ^ n) (indexV v).2.down))) : coordinate n degree := by
    exact scalarCover_node_sections A base baseK q hq old Knode hOld hBase
      V indexV eV holdV hbase ((Scheme.Modules.pullback q).obj (L n))
      (pullSection q (L n) (sectionHom n)) _ degree
      (fun s => (Polynomial.map (Algebra.TensorProduct.includeRight :
        A s →ₐ[R] K ⊗[R] A s).toRingHom (P s)) ^ n) hc
  exact ⟨fun n => transfer n (2 * n) (hcoordinates.1 n),
    fun prime hp => transfer _ _ (hcoordinates.2 prime hp)⟩

include hq hopen hOldBase hU hchart in
/-- The arithmetic section family constructs the coordinates on both charts
of every projective node of the prescribed scalar fibre. -/
theorem scalarWord_coordinates {XK Z : Scheme.{u}}
    (n : XK ⟶ X) (r : XK ⟶ Z) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback n).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (W : X.OpenCover.{u}) {I : Type u} (index : U.I₀ → I)
    (PK : I → Scheme.{u}) (g : ∀ i, PK i ⟶ XK) (c : ∀ i, PK i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ d i, (Scheme.Modules.pullback (c i)).obj (LK d) ≅ unitModule (PK i))
    (z : ∀ i, PK (index i) ⟶ U.X i)
    (hwhole : ∀ i, z i ≫ U.f i = g (index i) ≫ n)
    (hfamily : ∀ d, scalarPolynomialSectionFamily n r (L d) (LK d) (EL d)
      W U index PK g c hc (Epoly d) z hwhole (sectionHom d)
      (fun i => (eU i).hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial (A (indexU i).1)))).inv
          (sectionChartPolynomial (2 * d) (P (indexU i).1 ^ d) (indexU i).2.down)))) :
    scalarWordCoordinateData A baseK q old L sectionHom (scalarWordPolynomial A P) := by
  obtain ⟨F, _harithmetic, hfield⟩ := specializedWord_sections base baseK q hq
    n r L LK EL W U index PK g c hc Epoly z hwhole
    (fun i => A (indexU i).1) eU hU sectionHom
    (fun i => P (indexU i).1) (fun i => (indexU i).2) hfamily
  exact node_coordinates A base baseK q hq old hopen hOldBase U indexU eU
    hchart L sectionHom P F hfield

end Generic

section Append

private def stageRings {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero
    K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroups.ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i) :
    {s : Finset ((AppendChartData.I input)) // s.Nonempty} ⥤ CommAlgCat.{u} S :=
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  fixedFibreDiagram (R := S) (M := S) ((AppendChartData.N input))

/-- The cocone projection and its component structural maps determine the
base equation of every projective node. -/
theorem projectiveCocone_node_base {R : Type u} [CommRing R]
    {J : Type u} [Category J] (N : J ⥤ CommAlgCat.{u} R)
    (D : Jᵒᵖ ⥤ Scheme.{u}) (eP : ∀ s, D.obj (.op s) ≅ line (N.obj s))
    (cD : Cocone D) (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (hπ : ∀ s, π.app (.op s) = (eP s).hom ≫
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)))
    (q : cD.pt ⟶ cG.pt.left)
    (hleg : ∀ s, cD.ι.app (.op s) ≫ q = π.app (.op s) ≫ (cG.ι.app (.op s)).left)
    (base : cD.pt ⟶ Spec (.of R)) (hbase : base = q ≫ cG.pt.hom) :
    ∀ s, cD.ι.app (.op s) ≫ base = (eP s).hom ≫
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := by
  intro s
  calc
    _ = (cD.ι.app (.op s) ≫ q) ≫ cG.pt.hom := by rw [hbase, Category.assoc]
    _ = (π.app (.op s) ≫ (cG.ι.app (.op s)).left) ≫ cG.pt.hom :=
      congrArg (fun a => a ≫ cG.pt.hom) (hleg s)
    _ = π.app (.op s) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := by
      have hs : (cG.ι.app (.op s)).left ≫ cG.pt.hom =
          Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s))) := (cG.ι.app (.op s)).w
      exact congrArg (fun a => π.app (.op s) ≫ a) hs
    _ = _ := congrArg (fun a => a ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (N.obj s)))) (hπ s)

private def terminalRings {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero :
    CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroups.ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (T : Type u) [tComm : CommRing T] [tAlg : Algebra S T] :
    {s : Finset ((AppendChartData.I input)) // s.Nonempty} ⥤ CommAlgCat.{u} T :=
  fixedFibreDiagram (R := T) (M := T) (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
      input)

/-- The retained append stage and the terminal scalar model share their node
indices, nested coefficient rings, and section-coordinate family. -/
def appendStageCoordinateData {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero :
    CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroups.ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X : Scheme.{u}} {base : X ⟶ Spec (.of S)}
    {m : bsdhScheme G (word ++ [i]) ⟶ X} (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G word
        i S hS₀ input context X base m)
    {T : Type u} [tComm : CommRing T] [tAlg : Algebra S T] {XT : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X)
    {κ : Type u} [κComm : CommRing κ] [κAlg : Algebra T κ] {Y : Scheme.{u}}
    (baseκ : Y ⟶ Spec (.of κ)) (qκ : Y ⟶ XT)
    (L : ℕ → XT.Modules) (sectionHom : ∀ n, unitModule XT ⟶ L n)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        tAlg).obj (singletonIndex j))) : Prop :=
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  ∃ old : ∀ s, line ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj s) ⟶ X,
    (∀ s, old s ≫ (AppendChartStage.q d) = coefficient S₀ S
      (((AppendChartData.N input)).obj s) ≫
      (((AppendChartContext.eP context)) s).inv ≫
        ((AppendChartContext.cD context)).ι.app (.op s)) ∧
    ∃ oldT : ∀ s, line ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        tAlg).obj s) ⟶ XT,
      (∀ s, oldT s ≫ qT = coefficient S T ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input).obj s) ≫ old s) ∧
      (∀ s, oldT s ≫ baseT = nodeBase S T ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input).obj s)) ∧
      (∀ s, IsPullback (coefficient S T ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input).obj s)) (oldT s) (old s) qT) ∧
      scalarWordCoordinateData (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T
          tComm tAlg).obj baseκ qκ oldT L sectionHom
        (fun n s => nodePolynomial (fixedFibreDiagram (R := κ) (M := κ) (@terminalRings.{u} K kField
            kClosed kZero S₀ S G word i hS₀ input T tComm tAlg))
          (matchingScalarPolynomial (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀
              input T tComm tAlg)
            (fixedFibreDiagram (R := κ) (M := κ) (@terminalRings.{u} K kField kClosed kZero S₀ S G
                word i hS₀ input T tComm tAlg))
            (fixedScalarMap T κ (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T
                tComm tAlg)) Q) n
          ((AppendChartData.sel input)) s)

/-- The original atlas, retained scalar squares, and arithmetic section
family construct both projective-node chart coordinates on the prescribed
fibre, with its finite cover chosen independently of the degree. -/
theorem appendStage_word_coordinates {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K]
    [kZero : CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroups.ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (context : AppendChartContext input)
    {X : Scheme.{u}} (base : X ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ X) (d : @AppendChartStage.{u} K kField kClosed kZero S₀ G word
        i S hS₀ input context X base m)
    (cG : Cocone (((AppendChartData.N input)).op ⋙ algSpec (.of S₀)))
    (π : ((AppendChartContext.D context)) ⟶
      ((AppendChartData.N input)).op ⋙ algSpec (.of S₀) ⋙
        Over.forget (Spec (.of S₀)))
    (hπ : ∀ s, π.app (.op s) = (((AppendChartContext.eP context)) s).hom ≫
      projectiveToSpec (((AppendChartData.N input)).obj s) (ULift.{u} (Fin 2)))
    (qOld : ((AppendChartContext.cD context)).pt ⟶ cG.pt.left)
    (hleg : ∀ s, ((AppendChartContext.cD context)).ι.app (.op s) ≫ qOld =
      π.app (.op s) ≫ (cG.ι.app (.op s)).left)
    (hbaseOld : (AppendChartContext.base context) = qOld ≫ cG.pt.hom)
    (hd : IsPullback (AppendChartStage.q d) base ((AppendChartContext.base context))
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    {T : Type u} [tComm : CommRing T] [tAlg : Algebra S T] {XT : Scheme.{u}}
    (baseT : XT ⟶ Spec (.of T)) (qT : XT ⟶ X)
    (hT : IsPullback qT baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (U : XT.OpenCover.{u}) [Finite U.I₀]
    (indexT : U.I₀ ≃ (AppendChartStage.V d).I₀)
    (eT : ∀ j, U.X j ≅ Spec (.of (Polynomial
      ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm tAlg).obj
          ((AppendChartStage.index d) (indexT j)).1))))
    (holdT : ∀ j, U.f j ≫ qT = (eT j).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight :
          (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
              ((AppendChartStage.index d) (indexT j)).1 →ₐ[S]
            T ⊗[S] (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
                ((AppendChartStage.index d) (indexT j)).1).toRingHom)) ≫
        ((AppendChartStage.eV d) (indexT j)).inv ≫ (AppendChartStage.V d).f (indexT j))
    (hbaseT : ∀ j, U.f j ≫ baseT = (eT j).hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap T (Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input
          T tComm tAlg).obj ((AppendChartStage.index d) (indexT j)).1)))))
    {κ : Type u} [κComm : CommRing κ] [κAlg : Algebra T κ] {Y XK Z : Scheme.{u}}
    (baseκ : Y ⟶ Spec (.of κ)) (qκ : Y ⟶ XT)
    (hκ : IsPullback qκ baseκ baseT (Spec.map (CommRingCat.ofHom (algebraMap T κ))))
    (n : XK ⟶ XT) (r : XK ⟶ Z)
    (L : ℕ → XT.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ degree, (Scheme.Modules.pullback n).obj (L degree) ≅
      (Scheme.Modules.pullback r).obj (LK degree))
    (W : XT.OpenCover.{u}) {I : Type u} (index : U.I₀ → I)
    (PK : I → Scheme.{u}) (g : ∀ i, PK i ⟶ XK) (c : ∀ i, PK i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ degree i, (Scheme.Modules.pullback (c i)).obj (LK degree) ≅ unitModule (PK i))
    (z : ∀ j, PK (index j) ⟶ U.X j)
    (hwhole : ∀ j, z j ≫ U.f j = g (index j) ≫ n)
    (sectionHom : ∀ degree, unitModule XT ⟶ L degree)
    (Q : ∀ j, Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        tAlg).obj (singletonIndex j)))
    (hfamily : ∀ degree, scalarPolynomialSectionFamily n r (L degree) (LK degree) (EL degree)
      W U index PK g c hc (Epoly degree) z hwhole (sectionHom degree)
      (fun j => (eT j).hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i
            hS₀ input T tComm tAlg).obj
          ((AppendChartStage.index d) (indexT j)).1)))).inv
          (sectionChartPolynomial (2 * degree)
            (singletonPolynomial (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input
                T tComm tAlg) Q ((AppendChartData.sel input))
              ((AppendChartStage.index d) (indexT j)).1 ^ degree)
            ((AppendChartStage.index d) (indexT j)).2.down)))) :
    @appendStageCoordinateData.{u} K kField kClosed kZero S₀ S G word i hS₀ input context X base m d
        T tComm tAlg XT baseT qT κ κComm κAlg Y baseκ qκ L sectionHom Q := by
  classical
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  have hbase₀ := projectiveCocone_node_base ((AppendChartData.N input))
    ((AppendChartContext.D context)) ((AppendChartContext.eP context))
    ((AppendChartContext.cD context)) cG π hπ qOld hleg
    ((AppendChartContext.base context)) hbaseOld
  have hcover : ∀ (Y : Scheme.{u}) (f : Y ⟶ ((AppendChartContext.cD context)).pt)
      (y : Y), ∃ s, ∃ z : (pullback f
        (((AppendChartContext.cD context)).ι.app (.op s)) : Scheme.{u}),
      pullback.fst f (((AppendChartContext.cD context)).ι.app (.op s)) z = y := by
    intro Y f y
    obtain ⟨s, z, hz⟩ := (AppendChartContext.hCover context) Y f y
    exact ⟨s.unop, z, hz⟩
  obtain ⟨old, hOld, hBase, _hCart, hOpen, _htop, _htransition⟩ :=
    exists_scalar_projective_nodes ((AppendChartData.N input))
      ((AppendChartContext.D context)) ((AppendChartContext.eP context))
      ((AppendChartContext.cD context))
      (fun s => (AppendChartContext.hOpen context) (.op s)) hcover
      ((AppendChartContext.base context)) hbase₀ base (AppendChartStage.q d) hd
  have hold (j : (AppendChartStage.V d).I₀) : (AppendChartStage.V d).f j ≫ (AppendChartStage.q d) =
      ((AppendChartStage.eV d) j).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight : ((AppendChartData.N input)).obj
          ((AppendChartStage.index d) j).1 →ₐ[S₀]
            S ⊗[S₀] ((AppendChartData.N input)).obj
              ((AppendChartStage.index d) j).1).toRingHom)) ≫
      projectiveLinePolynomialChart (((AppendChartData.N input)).obj
        ((AppendChartStage.index d) j).1) ((AppendChartStage.index d) j).2 ≫
        (((AppendChartContext.eP context)) ((AppendChartStage.index d) j).1).inv ≫
          ((AppendChartContext.cD context)).ι.app (.op ((AppendChartStage.index d) j).1) :=
    AppendChartStage.hold d j
  have hchart (j : (AppendChartStage.V d).I₀) : ((AppendChartStage.eV d) j).inv ≫
      (AppendChartStage.V d).f j = projectiveLinePolynomialChart
        ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
            ((AppendChartStage.index d) j).1) ((AppendChartStage.index d) j).2 ≫
          old ((AppendChartStage.index d) j).1 :=
    (scalarCover_node_chart ((AppendChartData.N input)).obj
      ((AppendChartContext.base context)) base (AppendChartStage.q d) hd
      (fun s => (((AppendChartContext.eP context)) s).inv ≫
        ((AppendChartContext.cD context)).ι.app (.op s)) old hOld hBase
      (AppendChartStage.V d) (AppendChartStage.index d) (AppendChartStage.eV d) hold
      (AppendChartStage.hbase d) j).symm
  choose oldT hOldT hBaseT hCartT hOpenT using fun s =>
    @scalar_node S T ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj s) _ _ _
        _
      (CommAlgCat.algebra ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj s))
          X XT base baseT qT hT
      (old s) (hOpen s) (hBase s)
  let indexU := indexT.trans (AppendChartStage.index d)
  have hholdT (j : U.I₀) : U.f j ≫ qT = (eT j).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
        (Algebra.TensorProduct.includeRight : (@stageRings.{u} K kField kClosed kZero S₀ S G word i
            hS₀ input).obj (indexU j).1 →ₐ[S]
          T ⊗[S] (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj (indexU
              j).1).toRingHom)) ≫
        projectiveLinePolynomialChart ((@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀
            input).obj (indexU j).1) (indexU j).2 ≫
          old (indexU j).1 := by
    exact (holdT j).trans (congrArg (fun a => (eT j).hom ≫ _ ≫ a) (hchart (indexT j)))
  have hchartT (j : U.I₀) : (eT j).inv ≫ U.f j =
      projectiveLinePolynomialChart ((@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀
          input T tComm tAlg).obj (indexU j).1) (indexU j).2 ≫
        oldT (indexU j).1 :=
    (scalarCover_node_chart (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
        base baseT qT hT old oldT hOldT hBaseT
      U indexU eT hholdT hbaseT j).symm
  refine ⟨old, hOld, oldT, hOldT, hBaseT, hCartT, ?_⟩
  have hcoords := scalarWord_coordinates (@terminalRings.{u} K kField kClosed kZero S₀ S G word i
      hS₀ input T tComm tAlg).obj baseT baseκ qκ hκ oldT
    hOpenT hBaseT U indexU eT hbaseT hchartT L sectionHom
    (singletonPolynomial (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T tComm
        tAlg) Q ((AppendChartData.sel input)))
    n r LK EL W index PK g c hc Epoly z hwhole hfamily
  exact Eq.mp (congrArg
    (scalarWordCoordinateData (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input T
        tComm tAlg).obj baseκ qκ oldT L sectionHom)
    (scalarWordPolynomial_node (K := κ) (@terminalRings.{u} K kField kClosed kZero S₀ S G word i hS₀
        input T tComm tAlg) Q
      ((AppendChartData.sel input)))) hcoords

end Append

end SchubertGeometry.RetainedCharacter
