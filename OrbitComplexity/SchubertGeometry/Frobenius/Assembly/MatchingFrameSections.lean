import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameOverlaps
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedAffineCovariance
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching line frames on the retained open ranges

Inverse coframes give sections over the image of the top open. A separate
open equality transports those sections to the open range. Scalar transport
is proved over arbitrary open immersions before applying it to the matching
line and its inverse character-power transitions.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter Polynomial

noncomputable section
universe u

namespace SchubertGeometry.RetainedCharacter

open private originalLeg originalLegOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitFrames
open private retainedChartRange retainedCoordinateIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

private theorem image_top_range {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    j ''ᵁ (⊤ : X.Opens) = j.opensRange := j.image_top_eq_opensRange

private def imageSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (x : Γ((Scheme.Modules.pullback j).obj M, ⊤)) :
    Γ(M, j ''ᵁ (⊤ : X.Opens)) :=
  (M.restrictAppIso j ⊤).hom
    ((((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).val.app (op ⊤)).hom x)

private def rangeSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (x : Γ((Scheme.Modules.pullback j).obj M, ⊤)) : Γ(M, j.opensRange) :=
  M.presheaf.map (eqToHom (image_top_range j).symm).op (imageSection j M x)

private def rangeScalar {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (a : Γ(X, ⊤)) : Γ(Y, j.opensRange) :=
  Y.presheaf.map (eqToHom (image_top_range j).symm).op ((j.appIso ⊤).inv a)

private theorem imageSection_smul {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (a : Γ(X, ⊤)) (x : Γ((Scheme.Modules.pullback j).obj M, ⊤)) :
    imageSection j M (a • x) = (j.appIso ⊤).inv a • imageSection j M x := by
  let f := (((Scheme.Modules.restrictFunctorIsoPullback j).inv.app M).val.app (op ⊤)).hom
  have hf := f.map_smul a x
  have he := ConcreteCategory.congr_hom (Scheme.Modules.smul_restrictAppIso_hom j M ⊤ a) (f x)
  exact (congrArg (fun z => (M.restrictAppIso j ⊤).hom z) hf).trans he

private theorem rangeSection_smul {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (a : Γ(X, ⊤)) (x : Γ((Scheme.Modules.pullback j).obj M, ⊤)) :
    rangeSection j M (a • x) = rangeScalar j a • rangeSection j M x := by
  have hi := imageSection_smul j M a x
  have hr := Scheme.Modules.map_smul M (eqToHom (image_top_range j).symm)
    ((j.appIso ⊤).inv a) (imageSection j M x)
  exact (congrArg
    (fun z => M.presheaf.map (eqToHom (image_top_range j).symm).op z) hi).trans hr

private theorem rangeSection_change {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (x y : Γ((Scheme.Modules.pullback j).obj M, ⊤)) (a : Γ(X, ⊤))
    (h : x = a • y) : rangeSection j M x = rangeScalar j a • rangeSection j M y :=
  (congrArg (rangeSection j M) h).trans (rangeSection_smul j M a y)

private theorem restriction_self {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : Γ(M, U)) : M.presheaf.map (homOfLE (le_refl U)).op e = e := by
  have hi : (homOfLE (le_refl U)).op = 𝟙 (op U) := Subsingleton.elim _ _
  exact ConcreteCategory.congr_hom
    ((congrArg M.presheaf.map hi).trans (CategoryTheory.Functor.map_id M.presheaf (op U))) e

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

/-- The inverse of the adjusted matching coframe, evaluated at one, gives
the line frame on the corresponding open range of the retained scheme. -/
def retainedMatchingFrameSection (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (d : (N.obj s)ˣ) :
    Γ(matchingModule N cN delta n, retainedChartRange N cN hcN s) :=
  @rangeSection _ _ (originalLeg N cN s) (originalLegOpen N cN hcN s)
    (matchingModule N cN delta n)
    (((adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).inv.val.app (op ⊤)).hom
      (1 : Γ(Spec (.of (N.obj s)), ⊤)))

/-- The full prior-frame factor on an intersection is the inverse adjusted
matching-unit power, transported to its open range. -/
def retainedMatchingFrameFactor (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    Γ(cN.pt.left, retainedChartRange N cN hcN s) :=
  @rangeScalar _ _ (originalLeg N cN s) (originalLegOpen N cN hcN s)
    ((Scheme.ΓSpecIso (.of (N.obj s))).inv
      ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s))

/-- The transported line frames on each common intersection differ by the
constructed inverse character-power factor, including both retained units. -/
theorem retainedMatchingFrame_change (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ) :
    retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d =
      retainedMatchingFrameFactor N cN hcN delta n s j hj k hk d e •
        retainedMatchingFrameSection N cN hcN delta n hco hn s k hk e := by
  have h := adjustedMatchingFrame_section N cN hcN delta n hco hn s j hj k hk d e
  exact @rangeSection_change _ _ (originalLeg N cN s) (originalLegOpen N cN hcN s)
    (matchingModule N cN delta n)
    (((adjustedMatchingFrame N cN hcN delta n hco hn s j hj d).inv.val.app (op ⊤)).hom
      (1 : Γ(Spec (.of (N.obj s)), ⊤)))
    (((adjustedMatchingFrame N cN hcN delta n hco hn s k hk e).inv.val.app (op ⊤)).hom
      (1 : Γ(Spec (.of (N.obj s)), ⊤)))
    ((Scheme.ΓSpecIso (.of (N.obj s))).inv
      ((((delta s j hj k hk * d * e⁻¹) ^ n)⁻¹ : (N.obj s)ˣ) : N.obj s)) h

section Cartier
variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p] [Algebra K R]

/-- On the common retained intersection, the two constructed line frames give
the affine prior-trace comparison with the full inverse transition factor. -/
theorem retainedMatchingFrameTrace
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta n) ⟶
      SheafOfModules.unit cN.pt.left.ringCatSheaf)
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) (d e : (N.obj s)ˣ)
    (hp : 0 < p) (a : (N.obj s)ˣ) (b : N.obj s) (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    let g := retainedMatchingFrameFactor N cN hcN delta n s j hj k hk d e
    let g' := (retainedCoordinateIso N cN hcN s).hom g
    polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ s
        (retainedMatchingFrameSection N cN hcN delta n hco hn s k hk e))
      (C (g' * (↑(a⁻¹) : N.obj s) ^ (p - 1)) * Q.comp (C (a : N.obj s) * X + C b)) =
    (polynomialTraceOfOperator (K := K)
      (ProjectiveCartier.retainedTwistedPriorOperator N cN hcN base
        (matchingModule N cN delta n) Θ s
        (retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d)) Q).comp
          (C (a : N.obj s) * X + C b) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let M := matchingModule N cN delta n
  let U := retainedChartRange N cN hcN s
  let es := retainedMatchingFrameSection N cN hcN delta n hco hn s j hj d
  let et := retainedMatchingFrameSection N cN hcN delta n hco hn s k hk e
  let g := retainedMatchingFrameFactor N cN hcN delta n s j hj k hk d e
  have hsec := retainedMatchingFrame_change N cN hcN delta n hco hn s j hj k hk d e
  have he : M.presheaf.map (homOfLE (le_refl U)).op es = g • et :=
    (restriction_self M U es).trans hsec
  have htrace := ProjectiveCartier.retainedAffinePriorTrace_map N cN hcN base M Θ
    (𝟙 s) es et g (le_refl U) he hp a b Q
  have hmap : (N.map (𝟙 s)).hom.toRingHom = RingHom.id (N.obj s) :=
    congrArg (fun f : N.obj s ⟶ N.obj s => f.hom.toRingHom)
      (CategoryTheory.Functor.map_id N s)
  simpa only [hmap, Polynomial.map_id] using htrace

end Cartier

-- GAP: Restricting the coframes from a larger retained index to this common
-- intersection still requires their whole-map naturality comparison. The
-- statements here construct both frames and their factor directly on the
-- common intersection; they do not identify an incoming coframe by assumption.
-- The scalar's image under retainedCoordinateIso is kept explicit. Its
-- identification with the coefficient in N.obj s requires the generic
-- comparison of that coordinate isomorphism with the open-range transport.

end SchubertGeometry.RetainedCharacter
