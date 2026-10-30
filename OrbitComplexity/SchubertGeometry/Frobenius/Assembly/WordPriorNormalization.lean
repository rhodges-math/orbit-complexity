import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CoframeSectionValues
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoordinateIso
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization from the retained matching section

The coefficient of the retained section is obtained from its whole coframe
identity. A normalized global twisted functional therefore gives the prior
normalization in the corresponding adjusted line frame, for every power.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
namespace SchubertGeometry.RetainedCharacter
universe u

open private rangeSection rangeScalar imageSection image_top_range rangeSection_smul
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
open private chartCoordinateIso chartTwistedOperator retainedChartRange retainedCoordinateIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private pullSection
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem rangeSection_pullSection {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (L : Y.Modules) (s : unitModule Y ⟶ L) :
    rangeSection j L
        (((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).app ⊤
          (1 : Γ(X, ⊤))) =
      L.presheaf.map (homOfLE (le_top : j.opensRange ≤ ⊤)).op
        (s.app ⊤ (1 : Γ(Y, ⊤))) := by
  have hi := ProjectiveCartier.imageSection_pullSection j L s
  change imageSection j L
      (((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).app ⊤
        (1 : Γ(X, ⊤))) = _ at hi
  change L.presheaf.map (eqToHom (image_top_range j).symm).op
    (imageSection j L
      (((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).app ⊤
        (1 : Γ(X, ⊤)))) = _
  rw [hi]
  have hm : (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op ≫
      (eqToHom (image_top_range j).symm).op =
      (homOfLE (le_top : j.opensRange ≤ ⊤)).op := Subsingleton.elim _ _
  exact ConcreteCategory.congr_hom
    ((L.presheaf.map_comp _ _).symm.trans (congrArg L.presheaf.map hm))
    (s.app ⊤ (1 : Γ(Y, ⊤)))

private theorem chartPrior_from_coframe {K A : Type u} [CommRing K] [CommRing A]
    {p : ℕ} [ExpChar K p] {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of K)) (L : Y.Modules)
    (Θ : frobeniusRestriction K p base L ⟶ unitModule Y)
    (s : unitModule Y ⟶ L)
    (hnorm : Θ.app ⊤ (s.app ⊤ (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)))
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j]
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule (Spec (.of A))) (a : A)
    (hs : ((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s) ≫ E.hom =
      globalSectionsSmul (unitModule (Spec (.of A))) ((Scheme.ΓSpecIso (.of A)).inv a)) :
    chartTwistedOperator base L Θ j
      (rangeSection j L (E.inv.app ⊤ (1 : Γ(Spec (.of A), ⊤)))) a = 1 := by
  have hv := ProjectiveCartier.coframe_section_value
    ((Scheme.Modules.pullback j).obj L)
    ((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s) E
    ((Scheme.ΓSpecIso (.of A)).inv a) hs
  have hsec := (rangeSection_pullSection j L s).symm.trans
    ((congrArg (rangeSection j L) hv).trans
      (rangeSection_smul j L ((Scheme.ΓSpecIso (.of A)).inv a)
        (E.inv.app ⊤ (1 : Γ(Spec (.of A), ⊤)))))
  exact ProjectiveCartier.chartTwistedOperator_normalized base L Θ
    (s.app ⊤ (1 : Γ(Y, ⊤))) hnorm j
    (rangeSection j L (E.inv.app ⊤ (1 : Γ(Spec (.of A), ⊤))))
    (rangeScalar j ((Scheme.ΓSpecIso (.of A)).inv a)) a hsec
    (ProjectiveCartier.chartCoordinate_rangeScalar j a)

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (r : ∀ j, N.obj (singletonIndex j))
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (r j) =
        (N.map (singletonArrow s k hk)).hom (r k) * (delta s j hj k hk : N.obj s))

/-- Evaluation on the retained matching section gives the adjusted prior
normalization with the complete coefficient and character power. -/
theorem retainedPrior_normalized {K : Type u} [CommRing K] {p : ℕ} [ExpChar K p]
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      unitModule cN.pt.left)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app (coefficientMatchingSection N cN delta r hr n) ⊤).hom
        (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))
    (j : J) (d : (N.obj (singletonIndex j))ˣ) :
    ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
      (matchingModule N cN delta n) Θ (singletonIndex j)
      (retainedMatchingFrameSection N cN hcN delta n hco hn
        (singletonIndex j) j (Finset.mem_singleton_self j) d)
      ((r j * (d : N.obj (singletonIndex j))) ^ n) = 1 := by
  exact @chartPrior_from_coframe K (N.obj (singletonIndex j)) _ _ p _ cN.pt.left
    base (matchingModule N cN delta n) Θ
    (coefficientMatchingSection N cN delta r hr n) hnorm
    (originalLeg N cN (singletonIndex j))
    (originalLegOpen N cN hcN (singletonIndex j))
    (retainedUnitFrame N cN hcN delta n hco hn j d)
    ((r j * (d : N.obj (singletonIndex j))) ^ n)
    (retainedUnitFrame_section N cN hcN delta n hco hn r hr j d)

end SchubertGeometry.RetainedCharacter
