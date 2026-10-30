import OrbitComplexity.FrobeniusSplitting.Modules.RelativeFunctions
import OrbitComplexity.FrobeniusSplitting.Modules.RelativeScalars
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The character matching module on the same retained affine diagram -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting.RetainedCharacter

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (cG : Cocone (N.op ⋙ algSpec (.of R)))

private def singletonIndex (j : J) : {s : Finset J // s.Nonempty} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

private def singletonArrow (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) : FrobeniusSplitting.RetainedCharacter.singletonIndex j ⟶ s :=
  homOfLE (Finset.singleton_subset_iff.mpr hj)

/-- A node is the original affine leg into the chosen prior model. -/
def node (s : {s : Finset J // s.Nonempty}) : Over cG.pt.left :=
  Over.mk (cG.ι.app (.op s)).left

/-- The coefficient arrow gives the restriction map between the same legs. -/
def nodeMap {s t : {s : Finset J // s.Nonempty}} (f : s ⟶ t) :
    FrobeniusSplitting.RetainedCharacter.node N cG t ⟶ FrobeniusSplitting.RetainedCharacter.node N
        cG s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))
    (congrArg Over.Hom.left (cG.w f.op))

private def coefficientSection (s : {s : Finset J // s.Nonempty}) (x : N.obj s) :
    Γ((FrobeniusSplitting.RetainedCharacter.node N cG s).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (N.obj s))).inv x

private def localFunctions (j : J) : cG.pt.left.Modules :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsObj cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG
      (FrobeniusSplitting.RetainedCharacter.singletonIndex j))

private def overlapIndex :=
  Σ s : {s : Finset J // s.Nonempty}, {j : J // j ∈ s.val} × {k : J // k ∈ s.val}

private def overlapFunctions (b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J := J)) :
    cG.pt.left.Modules :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsObj cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG b.1)

private def localProduct : cG.pt.left.Modules := ∏ᶜ
    FrobeniusSplitting.RetainedCharacter.localFunctions N cG

private def overlapProduct : cG.pt.left.Modules := ∏ᶜ
    FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG

private def firstRestriction (b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J := J)) :
    FrobeniusSplitting.RetainedCharacter.localFunctions N cG b.2.1.val ⟶
        FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
    (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
        (FrobeniusSplitting.RetainedCharacter.singletonArrow b.1 b.2.1.val b.2.1.property))

private def secondRestriction (b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J := J)) :
    FrobeniusSplitting.RetainedCharacter.localFunctions N cG b.2.2.val ⟶
        FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
    (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
        (FrobeniusSplitting.RetainedCharacter.singletonArrow b.1 b.2.2.val b.2.2.property))

variable (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
    (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)

private def characterMultiplier (b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J := J)) :
    FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG b ⟶
        FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG b.1)
    (FrobeniusSplitting.RetainedCharacter.coefficientSection N cG b.1
      ((delta₀ b.1 b.2.1.val b.2.1.property b.2.2.val b.2.2.property : N.obj b.1) ^ n))

private def firstMatching : FrobeniusSplitting.RetainedCharacter.localProduct N cG ⟶
    FrobeniusSplitting.RetainedCharacter.overlapProduct N cG :=
  Pi.lift (fun b ↦ Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.1.val ≫
      FrobeniusSplitting.RetainedCharacter.firstRestriction N cG b)

private def secondMatching : FrobeniusSplitting.RetainedCharacter.localProduct N cG ⟶
    FrobeniusSplitting.RetainedCharacter.overlapProduct N cG :=
  Pi.lift (fun b ↦ Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.2.val ≫
    FrobeniusSplitting.RetainedCharacter.secondRestriction N cG b ≫
        FrobeniusSplitting.RetainedCharacter.characterMultiplier N cG delta₀ n b)

private theorem firstMatching_projection (b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J
    := J)) :
    FrobeniusSplitting.RetainedCharacter.firstMatching N cG ≫ Pi.π
        (FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG) b =
      Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.1.val ≫
          FrobeniusSplitting.RetainedCharacter.firstRestriction N cG b :=
  Pi.lift_comp_π _ b

private theorem secondMatching_projection (b : FrobeniusSplitting.RetainedCharacter.overlapIndex
    (J := J)) :
    FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n ≫ Pi.π
        (FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG) b =
      Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.2.val ≫
        FrobeniusSplitting.RetainedCharacter.secondRestriction N cG b ≫
            FrobeniusSplitting.RetainedCharacter.characterMultiplier N cG delta₀ n b :=
  Pi.lift_comp_π _ b

/-- The sheaf is constructed from coefficient matching f_j = delta_jk^n f_k.
Its unit bases therefore have the inverse-character transition. -/
def matchingModule : cG.pt.left.Modules :=
  equalizer (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
      (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n)

/-- Each coordinate is the projection of the matching equalizer. -/
def coordinate (j : J) :
    FrobeniusSplitting.RetainedCharacter.matchingModule N cG delta₀ n ⟶
        FrobeniusSplitting.RetainedCharacter.localFunctions N cG j :=
  equalizer.ι (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
      (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n) ≫
    Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) j

/-- The defining regular-function comparison holds on every original overlap. -/
theorem coordinate_matching (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) (k : J) (hk : k ∈ s.val) :
    FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n j ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
            (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
            (FrobeniusSplitting.RetainedCharacter.singletonArrow s j hj)) =
      FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n k ≫
        FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
            (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
            (FrobeniusSplitting.RetainedCharacter.singletonArrow s k hk)) ≫
          FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
              (FrobeniusSplitting.RetainedCharacter.node N cG s)
            (FrobeniusSplitting.RetainedCharacter.coefficientSection N cG s ((delta₀ s j hj k hk :
                N.obj s) ^ n)) := by
  let b : FrobeniusSplitting.RetainedCharacter.overlapIndex (J := J) := ⟨s, ⟨j, hj⟩, ⟨k, hk⟩⟩
  let i := equalizer.ι (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
      (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n)
  let p := Pi.π (FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG) b
  let pj := Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) j
  let pk := Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) k
  let rj := FrobeniusSplitting.RetainedCharacter.firstRestriction N cG b
  let rk := FrobeniusSplitting.RetainedCharacter.secondRestriction N cG b
  let m := FrobeniusSplitting.RetainedCharacter.characterMultiplier N cG delta₀ n b
  have h := congrArg (fun z ↦ z ≫ p)
    (equalizer.condition (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
        (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n))
  change (i ≫ pj) ≫ rj = (i ≫ pk) ≫ rk ≫ m
  calc
    (i ≫ pj) ≫ rj = i ≫ (pj ≫ rj) := Category.assoc i pj rj
    _ = i ≫ (FrobeniusSplitting.RetainedCharacter.firstMatching N cG ≫ p) :=
      congrArg (fun z ↦ i ≫ z) (FrobeniusSplitting.RetainedCharacter.firstMatching_projection N cG
          b).symm
    _ = (i ≫ FrobeniusSplitting.RetainedCharacter.firstMatching N cG) ≫ p := (Category.assoc _ _
        _).symm
    _ = (i ≫ FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n) ≫ p := h
    _ = i ≫ (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n ≫ p) :=
        Category.assoc _ _ _
    _ = i ≫ (pk ≫ rk ≫ m) :=
      congrArg (fun z ↦ i ≫ z) (FrobeniusSplitting.RetainedCharacter.secondMatching_projection N
          cG delta₀ n b)
    _ = (i ≫ pk) ≫ rk ≫ m := (Category.assoc i pk (rk ≫ m)).symm

/-- local coordinate morphisms factor through the matching module when
and only when they satisfy the retained coefficient equations. -/
def lift {P : cG.pt.left.Modules} (f : ∀ j, P ⟶
    FrobeniusSplitting.RetainedCharacter.localFunctions N cG j)
    (hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.singletonArrow s j hj)) =
        f k ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.singletonArrow s k hk)) ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
                (FrobeniusSplitting.RetainedCharacter.node N cG s)
              (FrobeniusSplitting.RetainedCharacter.coefficientSection N cG s ((delta₀ s j hj k hk
                  : N.obj s) ^ n))) :
    P ⟶ FrobeniusSplitting.RetainedCharacter.matchingModule N cG delta₀ n :=
  equalizer.lift (Pi.lift f) (by
    apply Pi.hom_ext
    intro b
    let p := Pi.π (FrobeniusSplitting.RetainedCharacter.overlapFunctions N cG) b
    let pj := Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.1.val
    let pk := Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) b.2.2.val
    let rj := FrobeniusSplitting.RetainedCharacter.firstRestriction N cG b
    let rk := FrobeniusSplitting.RetainedCharacter.secondRestriction N cG b
    let m := FrobeniusSplitting.RetainedCharacter.characterMultiplier N cG delta₀ n b
    calc
      (Pi.lift f ≫ FrobeniusSplitting.RetainedCharacter.firstMatching N cG) ≫ p =
          Pi.lift f ≫ (FrobeniusSplitting.RetainedCharacter.firstMatching N cG ≫ p) :=
              Category.assoc _ _ _
      _ = Pi.lift f ≫ (pj ≫ rj) :=
        congrArg (fun z ↦ Pi.lift f ≫ z)
            (FrobeniusSplitting.RetainedCharacter.firstMatching_projection N cG b)
      _ = (Pi.lift f ≫ pj) ≫ rj := (Category.assoc _ _ _).symm
      _ = f b.2.1.val ≫ rj :=
        congrArg (fun z ↦ z ≫ rj) (Pi.lift_comp_π f b.2.1.val)
      _ = f b.2.2.val ≫ rk ≫ m :=
        hf b.1 b.2.1.val b.2.1.property b.2.2.val b.2.2.property
      _ = (Pi.lift f ≫ pk) ≫ rk ≫ m :=
        congrArg (fun z ↦ z ≫ rk ≫ m) (Pi.lift_comp_π f b.2.2.val).symm
      _ = Pi.lift f ≫ (pk ≫ rk ≫ m) := Category.assoc _ _ _
      _ = Pi.lift f ≫ (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n ≫ p) :=
        congrArg (fun z ↦ Pi.lift f ≫ z)
            (FrobeniusSplitting.RetainedCharacter.secondMatching_projection N cG delta₀ n b).symm
      _ = (Pi.lift f ≫ FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n) ≫ p :=
        (Category.assoc _ _ _).symm)

/-- The constructed morphism has the original local coordinate maps. -/
theorem lift_coordinate {P : cG.pt.left.Modules} (f : ∀ j, P ⟶
    FrobeniusSplitting.RetainedCharacter.localFunctions N cG j)
    (hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.singletonArrow s j hj)) =
        f k ≫ FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.singletonArrow s k hk)) ≫
            FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
                (FrobeniusSplitting.RetainedCharacter.node N cG s)
              (FrobeniusSplitting.RetainedCharacter.coefficientSection N cG s ((delta₀ s j hj k hk
                  : N.obj s) ^ n))) (j : J) :
    FrobeniusSplitting.RetainedCharacter.lift N cG delta₀ n f hf ≫
        FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n j = f j := by
  let i := equalizer.ι (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
      (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n)
  let p := Pi.π (FrobeniusSplitting.RetainedCharacter.localFunctions N cG) j
  have hi : FrobeniusSplitting.RetainedCharacter.lift N cG delta₀ n f hf ≫ i = Pi.lift f :=
      equalizer.lift_ι _ _
  change FrobeniusSplitting.RetainedCharacter.lift N cG delta₀ n f hf ≫ (i ≫ p) = f j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ p) hi).trans (Pi.lift_comp_π f j))

/-- Morphisms into the matching module are determined by the original
singleton-chart coordinates. -/
theorem coordinate_hom_ext {P : cG.pt.left.Modules}
    (f g : P ⟶ FrobeniusSplitting.RetainedCharacter.matchingModule N cG delta₀ n)
    (h : ∀ j, f ≫ FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n j = g ≫
        FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n j) : f = g := by
  apply (cancel_mono (equalizer.ι (FrobeniusSplitting.RetainedCharacter.firstMatching N cG)
    (FrobeniusSplitting.RetainedCharacter.secondMatching N cG delta₀ n))).1
  apply Pi.hom_ext
  intro j
  exact (Category.assoc f _ _).trans ((h j).trans (Category.assoc g _ _).symm)

end FrobeniusSplitting.RetainedCharacter
