import OrbitComplexity.FrobeniusSplitting.Modules.MatchingLimits
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.BaseCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameCocycle
import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctions
import OrbitComplexity.FrobeniusSplitting.Modules.OpenFunctionMaps
import Batteries.Tactic.Lint

/-! # Local frames for matching character modules -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter

private def functionsUnit (S : Scheme.{u}) (X : Over S) :
    SheafOfModules.unit S.ringCatSheaf ⟶ relativeFunctionsObj S X :=
  BaseCoordinates.unit S X

private theorem iso_cancel {C : Type*} [Category C] {A B T : C}
    (e : A ≅ B) {f g : T ⟶ A} (h : f ≫ e.hom = g ≫ e.hom) : f = g := by
  have hh := congrArg (fun z => z ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

private theorem assoc_four {C : Type*} [Category C] {A B D E T : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (k : E ⟶ T) :
    (f ≫ g ≫ h) ≫ k = f ≫ g ≫ (h ≫ k) := by simp only [Category.assoc]

private theorem functionsUnit_natural {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    functionsUnit S Y ≫ relativeFunctionsMap S f = functionsUnit S X :=
  BaseCoordinates.unit_natural f

private def weightedBaseCoordinate {U Y P X : Scheme.{u}}
    (j : U ⟶ Y) [hj : IsOpenImmersion j] (p : P ⟶ U) (q : X ⟶ Y) (k : P ⟶ X)
    [hk : IsOpenImmersion k] (H : IsPullback p k j q) (r : Γ(P, ⊤)) :
    SheafOfModules.unit U.ringCatSheaf ⟶
      (@Scheme.Modules.restrictFunctor _ _ j hj).obj
        (relativeFunctionsObj Y (Over.mk q)) :=
  BaseCoordinates.weighted j p q k H r

private theorem coordinateSection_map {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) (x : N.obj s) :
    (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (N.obj s))).inv x) =
      (Scheme.ΓSpecIso (.of (N.obj t))).inv ((N.map f).hom x) := by
  exact (congrArg
    (fun g : CommRingCat.of (N.obj s) ⟶ Γ(Spec (.of (N.obj t)), ⊤) ↦ g x)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (N.map f).hom.toRingHom))).symm

private theorem coefficientCoordinate_map
    {U Y P₁ P₂ X₁ X₂ : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (p₁ : P₁ ⟶ U) (p₂ : P₂ ⟶ U) (q₁ : X₁ ⟶ Y) (q₂ : X₂ ⟶ Y)
    (k₁ : P₁ ⟶ X₁) (k₂ : P₂ ⟶ X₂)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (H₁ : IsPullback p₁ k₁ j q₁) (H₂ : IsPullback p₂ k₂ j q₂)
    (M : Over.mk q₁ ⟶ Over.mk q₂) (T : Over.mk p₁ ⟶ Over.mk p₂)
    (hk : T.left ≫ k₂ = k₁ ≫ M.left) (r : Γ(P₂, ⊤)) :
    weightedBaseCoordinate j p₂ q₂ k₂ H₂ r ≫
        (Scheme.Modules.restrictFunctor j).map (relativeFunctionsMap Y M) ≫
          (openFunctionsBaseChange p₁ k₁ j q₁ H₁).hom =
      functionsUnit U (Over.mk p₁) ≫
        relativeFunctionsSmul U (Over.mk p₁) (T.left.appTop r) :=
  BaseCoordinates.weighted_map j p₁ p₂ q₁ q₂ k₁ k₂ H₁ H₂ M T hk r

private def frameIndex {J : Type u} (j : J) : {s : Finset J // s.Nonempty} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

private def frameInto {J : Type u} (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) : frameIndex j ⟶ s :=
  homOfLE (Finset.singleton_subset_iff.mpr hj)

private def combinedArrow {J : Type u} (u : {s : Finset J // s.Nonempty})
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    unionIndex u s ⟶ unionIndex u t := by
  classical
  apply homOfLE
  change u.val ∪ s.val ⊆ u.val ∪ t.val
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ hx
  · exact Finset.mem_union_right _ ((leOfHom f) hx)

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hmapOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hdirected : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)

private def specArrow {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    Spec (.of (N.obj t)) ⟶ Spec (.of (N.obj s)) :=
  Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)

omit hmapOpen hdirected in
private theorem specArrow_triangle {a b c : {s : Finset J // s.Nonempty}}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
    specArrow N g ≫ specArrow N f = specArrow N h := by
  let E := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  change E.map g.op ≫ E.map f.op = E.map h.op
  rw [← E.map_comp]
  exact congrArg E.map (Subsingleton.elim _ _)

private def originalLeg (s : {s : Finset J // s.Nonempty}) := (cG.ι.app (.op s)).left

include hcG in
private theorem originalLegOpen (s : {s : Finset J // s.Nonempty}) :
    IsOpenImmersion (originalLeg N cG s) := (retained_prior_charts N cG hcG).1 s

private def chartRestriction (u : {s : Finset J // s.Nonempty}) :=
  @Scheme.Modules.restrictFunctor _ _ (originalLeg N cG u) (originalLegOpen N cG hcG u)

private def localIntersection (u s : {s : Finset J // s.Nonempty}) :
    Over (Spec (.of (N.obj u))) := Over.mk (specArrow N (unionLeft u s))

private def localIntersectionMap (u : {s : Finset J // s.Nonempty})
    {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    localIntersection N u t ⟶ localIntersection N u s :=
  Over.homMk (specArrow N (combinedArrow u f))
    (specArrow_triangle N (unionLeft u s) (combinedArrow u f) (unionLeft u t))

private def localBC (u s : {s : Finset J // s.Nonempty}) :
    (chartRestriction N cG hcG u).obj (relativeFunctionsObj cG.pt.left
        (node N cG s)) ≅
      relativeFunctionsObj (Spec (.of (N.obj u))) (localIntersection N u s) :=
  @openFunctionsBaseChange _ _ _ _
    (specArrow N (unionLeft u s)) (specArrow N (unionRight u s))
    (originalLeg N cG u) (originalLeg N cG s)
    (originalLegOpen N cG hcG u) (hmapOpen (unionRight u s))
    (retained_overlap_square N cG hcG u s)

private def frameCoefficient (u : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ u.val) (k : J) :
    Γ(Spec (.of (N.obj (unionIndex u (frameIndex k)))), ⊤) :=
  BaseCoordinates.coefficient N delta₀ n u j hj k

private def candidateCoordinate (u : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ u.val) (k : J) :
    SheafOfModules.unit (Spec (.of (N.obj u))).ringCatSheaf ⟶
      (chartRestriction N cG hcG u).obj
        (relativeFunctionsObj cG.pt.left (node N cG (frameIndex k))) :=
  @weightedBaseCoordinate _ _ _ _ (originalLeg N cG u) (originalLegOpen N cG hcG u)
    (specArrow N (unionLeft u (frameIndex k))) (originalLeg N cG (frameIndex k))
    (specArrow N (unionRight u (frameIndex k))) (hmapOpen (unionRight u (frameIndex k)))
    (retained_overlap_square N cG hcG u (frameIndex k))
    (frameCoefficient N delta₀ n u j hj k)

private theorem candidateCoordinate_restrict (u : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ u.val) (s : {s : Finset J // s.Nonempty})
    (k : J) (hk : k ∈ s.val) :
    candidateCoordinate N cG hcG delta₀ n u j hj k ≫
        (chartRestriction N cG hcG u).map
          (relativeFunctionsMap cG.pt.left (nodeMap N cG (frameInto s k hk))) ≫
            (localBC N cG hcG u s).hom =
      functionsUnit (Spec (.of (N.obj u))) (localIntersection N u s) ≫
        relativeFunctionsSmul (Spec (.of (N.obj u))) (localIntersection N u s)
          ((localIntersectionMap N u (frameInto s k hk)).left.appTop
            (frameCoefficient N delta₀ n u j hj k)) := by
  have h : (localIntersectionMap N u (frameInto s k hk)).left ≫
      specArrow N (unionRight u (frameIndex k)) =
        specArrow N (unionRight u s) ≫ (nodeMap N cG (frameInto s k hk)).left :=
    (specArrow_triangle N (unionRight u (frameIndex k)) (combinedArrow u (frameInto s k hk))
      (frameInto s k hk ≫ unionRight u s)).trans
        (specArrow_triangle N (frameInto s k hk) (unionRight u s)
          (frameInto s k hk ≫ unionRight u s)).symm
  exact @coefficientCoordinate_map _ _ _ _ _ _ (originalLeg N cG u)
    (originalLegOpen N cG hcG u)
    (specArrow N (unionLeft u s)) (specArrow N (unionLeft u (frameIndex k)))
    (originalLeg N cG s) (originalLeg N cG (frameIndex k))
    (specArrow N (unionRight u s)) (specArrow N (unionRight u (frameIndex k)))
    (hmapOpen (unionRight u s)) (hmapOpen (unionRight u (frameIndex k)))
    (retained_overlap_square N cG hcG u s) (retained_overlap_square N cG hcG u (frameIndex k))
    (nodeMap N cG (frameInto s k hk)) (localIntersectionMap N u (frameInto s k hk)) h
    (frameCoefficient N delta₀ n u j hj k)


omit hmapOpen hdirected in
private theorem candidateCoefficient_matching (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val)
    (s : {s : Finset J // s.Nonempty}) (k : J) (hk : k ∈ s.val)
    (l : J) (hl : l ∈ s.val) :
    (show Γ((localIntersection N u s).left, ⊤) from
      (localIntersectionMap N u (frameInto s k hk)).left.appTop
        (frameCoefficient N delta₀ n u j hj k)) =
      (show Γ((localIntersection N u s).left, ⊤) from
        (specArrow N (unionRight u s)).appTop
          ((Scheme.ΓSpecIso (.of (N.obj s))).inv ((delta₀ s k hk l hl : N.obj s) ^ n))) *
        (show Γ((localIntersection N u s).left, ⊤) from
          (localIntersectionMap N u (frameInto s l hl)).left.appTop
            (frameCoefficient N delta₀ n u j hj l)) := by
  let dk := delta₀ (unionIndex u (frameIndex k))
    j ((leOfHom (unionLeft u (frameIndex k))) hj)
    k ((leOfHom (unionRight u (frameIndex k))) (Finset.mem_singleton_self k))
  let dl := delta₀ (unionIndex u (frameIndex l))
    j ((leOfHom (unionLeft u (frameIndex l))) hj)
    l ((leOfHom (unionRight u (frameIndex l))) (Finset.mem_singleton_self l))
  have h : Units.map (N.map (combinedArrow u (frameInto s k hk))).hom.toMonoidHom (dk⁻¹ ^ n) =
      Units.map (N.map (unionRight u s)).hom.toMonoidHom (delta₀ s k hk l hl ^ n) *
        Units.map (N.map (combinedArrow u (frameInto s l hl))).hom.toMonoidHom (dl⁻¹ ^ n) :=
    inverse_frame_overlap_cocycle N delta₀ hco hn n u s j hj k hk l hl
  have h' := congrArg (fun x : (N.obj (unionIndex u s))ˣ ↦
    (Scheme.ΓSpecIso (.of (N.obj (unionIndex u s)))).inv (x : N.obj (unionIndex u s))) h
  change (specArrow N (combinedArrow u (frameInto s k hk))).appTop
      ((Scheme.ΓSpecIso (.of (N.obj (unionIndex u (frameIndex k))))).inv (↑(dk⁻¹ ^ n))) =
    (specArrow N (unionRight u s)).appTop
      ((Scheme.ΓSpecIso (.of (N.obj s))).inv ((delta₀ s k hk l hl : N.obj s) ^ n)) *
      (specArrow N (combinedArrow u (frameInto s l hl))).appTop
        ((Scheme.ΓSpecIso (.of (N.obj (unionIndex u (frameIndex l))))).inv (↑(dl⁻¹ ^ n)))
  have hkmap := coordinateSection_map N (combinedArrow u (frameInto s k hk)) (↑(dk⁻¹ ^ n))
  have hrmap := coordinateSection_map N (unionRight u s) ((delta₀ s k hk l hl : N.obj s) ^ n)
  have hlmap := coordinateSection_map N (combinedArrow u (frameInto s l hl)) (↑(dl⁻¹ ^ n))
  exact hkmap.trans ((h'.trans
    (map_mul (Scheme.ΓSpecIso (.of (N.obj (unionIndex u s)))).inv.hom _ _)).trans
      (congrArg₂ (fun x y : Γ(Spec (.of (N.obj (unionIndex u s))), ⊤) => x * y)
        hrmap.symm hlmap.symm))

private theorem localBC_smul (u s : {s : Finset J // s.Nonempty}) (r : Γ((node N cG s).left, ⊤)) :
    (chartRestriction N cG hcG u).map
        (relativeFunctionsSmul cG.pt.left (node N cG s) r) ≫
          (localBC N cG hcG u s).hom =
      (localBC N cG hcG u s).hom ≫
        relativeFunctionsSmul (Spec (.of (N.obj u))) (localIntersection N u s)
          ((specArrow N (unionRight u s)).appTop r) :=
  @BaseCoordinates.baseChange_smul _ _ _ _ (originalLeg N cG u)
    (originalLegOpen N cG hcG u) (specArrow N (unionLeft u s)) (originalLeg N cG s)
    (specArrow N (unionRight u s)) (hmapOpen (unionRight u s))
    (retained_overlap_square N cG hcG u s) r

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "UnitFrames: candidateCoordinate_matching"
    (← IO.getStderr).flush

private theorem candidateCoordinate_matching
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val)
    (s : {s : Finset J // s.Nonempty}) (k : J) (hk : k ∈ s.val)
    (l : J) (hl : l ∈ s.val) :
    candidateCoordinate N cG hcG delta₀ n u j hj k ≫
        (chartRestriction N cG hcG u).map
          (relativeFunctionsMap cG.pt.left (nodeMap N cG (frameInto s k hk))) =
      candidateCoordinate N cG hcG delta₀ n u j hj l ≫
        (chartRestriction N cG hcG u).map
          (relativeFunctionsMap cG.pt.left (nodeMap N cG (frameInto s l hl))) ≫
        (chartRestriction N cG hcG u).map
          (relativeFunctionsSmul cG.pt.left (node N cG s)
            ((Scheme.ΓSpecIso (.of (N.obj s))).inv ((delta₀ s k hk l hl : N.obj s) ^ n))) := by
  let e := localBC N cG hcG u s
  let r : Γ((node N cG s).left, ⊤) :=
    (Scheme.ΓSpecIso (.of (N.obj s))).inv ((delta₀ s k hk l hl : N.obj s) ^ n)
  let a := functionsUnit (Spec (.of (N.obj u))) (localIntersection N u s)
  let ck : Γ((localIntersection N u s).left, ⊤) :=
    (localIntersectionMap N u (frameInto s k hk)).left.appTop
    (frameCoefficient N delta₀ n u j hj k)
  let cl : Γ((localIntersection N u s).left, ⊤) :=
    (localIntersectionMap N u (frameInto s l hl)).left.appTop
    (frameCoefficient N delta₀ n u j hj l)
  let rs : Γ((localIntersection N u s).left, ⊤) :=
    (specArrow N (unionRight u s)).appTop r
  let mk := (chartRestriction N cG hcG u).map
    (relativeFunctionsMap cG.pt.left (nodeMap N cG (frameInto s k hk)))
  let ml := (chartRestriction N cG hcG u).map
    (relativeFunctionsMap cG.pt.left (nodeMap N cG (frameInto s l hl)))
  let mr := (chartRestriction N cG hcG u).map
    (relativeFunctionsSmul cG.pt.left (node N cG s) r)
  let xk := candidateCoordinate N cG hcG delta₀ n u j hj k
  let xl := candidateCoordinate N cG hcG delta₀ n u j hj l
  have hk' : xk ≫ mk ≫ e.hom = a ≫ relativeFunctionsSmul _ _ ck :=
    candidateCoordinate_restrict N cG hcG delta₀ n u j hj s k hk
  have hl' : xl ≫ ml ≫ e.hom = a ≫ relativeFunctionsSmul _ _ cl :=
    candidateCoordinate_restrict N cG hcG delta₀ n u j hj s l hl
  have hm : mr ≫ e.hom = e.hom ≫ relativeFunctionsSmul _ _ rs :=
    localBC_smul N cG hcG u s r
  have hcoeff : ck = rs * cl := candidateCoefficient_matching N delta₀ n hco hn u j hj s k hk l hl
  change xk ≫ mk = xl ≫ ml ≫ mr
  apply iso_cancel e
  calc
    (xk ≫ mk) ≫ e.hom = a ≫ relativeFunctionsSmul _ _ ck :=
      (Category.assoc _ _ _).trans hk'
    _ = a ≫ relativeFunctionsSmul _ _ (rs * cl) :=
      congrArg (fun z ↦ a ≫ relativeFunctionsSmul _ _ z) hcoeff
    _ = a ≫ (relativeFunctionsSmul _ _ cl ≫
        relativeFunctionsSmul _ _ rs) :=
      congrArg (fun z ↦ a ≫ z) (relativeFunctionsSmul_mul _ _ rs cl)
    _ = (a ≫ relativeFunctionsSmul _ _ cl) ≫
        relativeFunctionsSmul _ _ rs := (Category.assoc _ _ _).symm
    _ = (xl ≫ ml ≫ e.hom) ≫ relativeFunctionsSmul _ _ rs :=
      congrArg (fun z ↦ z ≫ relativeFunctionsSmul _ _ rs) hl'.symm
    _ = xl ≫ ml ≫ (e.hom ≫ relativeFunctionsSmul _ _ rs) :=
      assoc_four xl ml e.hom (relativeFunctionsSmul _ _ rs)
    _ = xl ≫ ml ≫ (mr ≫ e.hom) := congrArg (fun z ↦ xl ≫ ml ≫ z) hm.symm
    _ = (xl ≫ ml ≫ mr) ≫ e.hom := (assoc_four xl ml mr e.hom).symm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "UnitFrames: localUnitFrame"
    (← IO.getStderr).flush

/-- The inverse character frame on an intersection chart. -/
def localUnitFrame
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) :
    SheafOfModules.unit (Spec (.of (N.obj u))).ringCatSheaf ⟶
      (chartRestriction N cG hcG u).obj (matchingModule N cG delta₀ n) := by
  let F := chartRestriction N cG hcG u
  let : PreservesLimitsOfSize.{u, u} F := @restrictPreservesLimits _ _
    (originalLeg N cG u) (originalLegOpen N cG hcG u)
  exact mappedLift N cG delta₀ n F
    (candidateCoordinate N cG hcG delta₀ n u j hj)
    (candidateCoordinate_matching N cG hcG delta₀ n hco hn u j hj)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "UnitFrames: localUnitFrame_coordinate"
    (← IO.getStderr).flush

/-- The inverse frame has its transition coefficient in each coordinate. -/
theorem localUnitFrame_coordinate
    (hco : ∀ s j hj k hk l hl,
      delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
        delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (u : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ u.val) (k : J) :
    localUnitFrame N cG hcG delta₀ n hco hn u j hj ≫
        (chartRestriction N cG hcG u).map (coordinate N cG delta₀ n k) =
      candidateCoordinate N cG hcG delta₀ n u j hj k := by
  let F := chartRestriction N cG hcG u
  let : PreservesLimitsOfSize.{u, u} F := @restrictPreservesLimits _ _
    (originalLeg N cG u) (originalLegOpen N cG hcG u)
  exact mappedLift_coordinate N cG delta₀ n F
    (candidateCoordinate N cG hcG delta₀ n u j hj)
    (candidateCoordinate_matching N cG hcG delta₀ n hco hn u j hj) k

end SchubertGeometry.RetainedCharacter
