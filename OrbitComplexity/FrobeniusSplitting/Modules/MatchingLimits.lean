import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Coordinate factorization through the original character module -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v w
namespace FrobeniusSplitting.RetainedCharacter

private def liftSingleton {J : Type u} (j : J) : {s : Finset J // s.Nonempty} :=
  ⟨{j}, Finset.singleton_nonempty j⟩

private def liftArrow {J : Type u} (s : {s : Finset J // s.Nonempty})
    (j : J) (hj : j ∈ s.val) : FrobeniusSplitting.RetainedCharacter.liftSingleton j ⟶ s :=
  homOfLE (Finset.singleton_subset_iff.mpr hj)

private def liftOverlap {J : Type u} :=
  Σ s : {s : Finset J // s.Nonempty}, {j : J // j ∈ s.val} × {k : J // k ∈ s.val}

variable {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)

private def liftFunctions (j : J) : cG.pt.left.Modules :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsObj cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG
      (FrobeniusSplitting.RetainedCharacter.liftSingleton j))

private def liftOverlapFunctions (b : FrobeniusSplitting.RetainedCharacter.liftOverlap (J := J)) :
    cG.pt.left.Modules :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsObj cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG b.1)

private def liftFirst (b : FrobeniusSplitting.RetainedCharacter.liftOverlap (J := J)) :
    FrobeniusSplitting.RetainedCharacter.liftFunctions N cG b.2.1.val ⟶
        FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
    (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
        (FrobeniusSplitting.RetainedCharacter.liftArrow b.1 b.2.1.val b.2.1.property))

private def liftSecond (b : FrobeniusSplitting.RetainedCharacter.liftOverlap (J := J)) :
    FrobeniusSplitting.RetainedCharacter.liftFunctions N cG b.2.2.val ⟶
        FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
    (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
        (FrobeniusSplitting.RetainedCharacter.liftArrow b.1 b.2.2.val b.2.2.property))

private def liftMultiplier (b : FrobeniusSplitting.RetainedCharacter.liftOverlap (J := J)) :
    FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG b ⟶
        FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG b :=
  FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
      (FrobeniusSplitting.RetainedCharacter.node N cG b.1)
    ((Scheme.ΓSpecIso (.of (N.obj b.1))).inv
      ((delta₀ b.1 b.2.1.val b.2.1.property b.2.2.val b.2.2.property : N.obj b.1) ^ n))

private def matchingFirst : (∏ᶜ FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) ⟶ ∏ᶜ
    FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG :=
  Pi.lift (fun b ↦ Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.1.val ≫
      FrobeniusSplitting.RetainedCharacter.liftFirst N cG b)

private def matchingSecond : (∏ᶜ FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) ⟶ ∏ᶜ
    FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG :=
  Pi.lift (fun b ↦ Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.2.val ≫
    FrobeniusSplitting.RetainedCharacter.liftSecond N cG b ≫
        FrobeniusSplitting.RetainedCharacter.liftMultiplier N cG delta₀ n b)

variable {D : Type v} [Category.{w} D] [HasLimitsOfSize.{u, u} D]
    (G : cG.pt.left.Modules ⥤ D) [PreservesLimitsOfSize.{u, u} G]

private def coordinateProduct {P : D} (f : ∀ j, P ⟶ G.obj
    (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG j)) :
    P ⟶ G.obj (∏ᶜ FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) :=
  Pi.lift f ≫ inv (piComparison G (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG))

private theorem coordinateProduct_projection {P : D}
    (f : ∀ j, P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG j)) (j : J) :
    FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f ≫ G.map (Pi.π
        (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) j) = f j :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ Pi.lift f ≫ z)
      (inv_piComparison_comp_map_π G (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG)
          j)).trans (Pi.lift_comp_π f j))

private theorem coordinateProduct_condition {P : D}
    (f : ∀ j, P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG j))
    (hf : ∀ b : FrobeniusSplitting.RetainedCharacter.liftOverlap (J := J),
      f b.2.1.val ≫ G.map (FrobeniusSplitting.RetainedCharacter.liftFirst N cG b) =
        f b.2.2.val ≫ G.map (FrobeniusSplitting.RetainedCharacter.liftSecond N cG b) ≫
          G.map (FrobeniusSplitting.RetainedCharacter.liftMultiplier N cG delta₀ n b)) :
    FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f ≫ G.map
        (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG) =
      FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f ≫ G.map
          (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n) := by
  let t := FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f
  let q := piComparison G (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG)
  apply (cancel_mono q).1
  apply Pi.hom_ext
  intro b
  let p := Pi.π (fun b ↦ G.obj (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG b)) b
  let r := G.map (Pi.π (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG) b)
  let pj := G.map (Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.1.val)
  let pk := G.map (Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.2.val)
  let a := G.map (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
  let g := G.map (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)
  let rj := G.map (FrobeniusSplitting.RetainedCharacter.liftFirst N cG b)
  let rk := G.map (FrobeniusSplitting.RetainedCharacter.liftSecond N cG b)
  let m := G.map (FrobeniusSplitting.RetainedCharacter.liftMultiplier N cG delta₀ n b)
  have hq : q ≫ p = r := piComparison_comp_π G
      (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG) b
  have ha : a ≫ r = pj ≫ rj := by
    have h : FrobeniusSplitting.RetainedCharacter.matchingFirst N cG ≫ Pi.π
        (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG) b =
        Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.1.val ≫
            FrobeniusSplitting.RetainedCharacter.liftFirst N cG b := Pi.lift_comp_π _ b
    simpa only [Functor.map_comp] using congrArg G.map h
  have hg : g ≫ r = pk ≫ rk ≫ m := by
    have h : FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n ≫ Pi.π
        (FrobeniusSplitting.RetainedCharacter.liftOverlapFunctions N cG) b =
        Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) b.2.2.val ≫
          FrobeniusSplitting.RetainedCharacter.liftSecond N cG b ≫
              FrobeniusSplitting.RetainedCharacter.liftMultiplier N cG delta₀ n b :=
              Pi.lift_comp_π _ b
    simpa only [Functor.map_comp] using congrArg G.map h
  change ((t ≫ a) ≫ q) ≫ p = ((t ≫ g) ≫ q) ≫ p
  calc
    ((t ≫ a) ≫ q) ≫ p = (t ≫ a) ≫ (q ≫ p) := Category.assoc _ _ _
    _ = (t ≫ a) ≫ r := congrArg (fun z ↦ (t ≫ a) ≫ z) hq
    _ = t ≫ (a ≫ r) := Category.assoc _ _ _
    _ = t ≫ (pj ≫ rj) := congrArg (fun z ↦ t ≫ z) ha
    _ = (t ≫ pj) ≫ rj := (Category.assoc _ _ _).symm
    _ = f b.2.1.val ≫ rj :=
      congrArg (fun z ↦ z ≫ rj) (FrobeniusSplitting.RetainedCharacter.coordinateProduct_projection
          N cG G f b.2.1.val)
    _ = f b.2.2.val ≫ rk ≫ m := hf b
    _ = (t ≫ pk) ≫ rk ≫ m :=
      congrArg (fun z ↦ z ≫ rk ≫ m)
          (FrobeniusSplitting.RetainedCharacter.coordinateProduct_projection N cG G f
          b.2.2.val).symm
    _ = t ≫ (pk ≫ rk ≫ m) := Category.assoc _ _ _
    _ = t ≫ (g ≫ r) := congrArg (fun z ↦ t ≫ z) hg.symm
    _ = (t ≫ g) ≫ r := (Category.assoc _ _ _).symm
    _ = (t ≫ g) ≫ (q ≫ p) := congrArg (fun z ↦ (t ≫ g) ≫ z) hq.symm
    _ = ((t ≫ g) ≫ q) ≫ p := (Category.assoc _ _ _).symm

/-- Coordinate factorization into a matching module after a limit-preserving functor. -/
def mappedLift {P : D} (f : ∀ j, P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.liftFunctions N
    cG j))
    (hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s j hj))) =
        f k ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s k hk))) ≫
          G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
              (FrobeniusSplitting.RetainedCharacter.node N cG s)
            ((Scheme.ΓSpecIso (.of (N.obj s))).inv
              ((delta₀ s j hj k hk : N.obj s) ^ n)))) :
    P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.matchingModule N cG delta₀ n) := by
  let hSmall : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink G
  let hShape : PreservesLimitsOfShape WalkingParallelPair G :=
    hSmall.preservesLimitsOfShape (J := WalkingParallelPair)
  let : PreservesLimit (parallelPair (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
      (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)) G :=
    hShape.preservesLimit
  exact equalizer.lift (FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f)
      (FrobeniusSplitting.RetainedCharacter.coordinateProduct_condition N cG delta₀ n G f
        (fun b ↦ hf b.1 b.2.1.val b.2.1.property b.2.2.val b.2.2.property)) ≫
    (PreservesEqualizer.iso G (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
        (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)).inv

private theorem mappedLift_inclusion {P : D}
    (f : ∀ j, P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG j))
    (hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s j hj))) =
        f k ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s k hk))) ≫
          G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
              (FrobeniusSplitting.RetainedCharacter.node N cG s)
            ((Scheme.ΓSpecIso (.of (N.obj s))).inv
              ((delta₀ s j hj k hk : N.obj s) ^ n)))) :
    FrobeniusSplitting.RetainedCharacter.mappedLift N cG delta₀ n G f hf ≫
      G.map (equalizer.ι (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
          (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)) =
        FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f := by
  let hSmall : PreservesLimitsOfSize.{0, 0} G := preservesLimitsOfSize_shrink G
  let hShape : PreservesLimitsOfShape WalkingParallelPair G :=
    hSmall.preservesLimitsOfShape (J := WalkingParallelPair)
  let : PreservesLimit (parallelPair (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
      (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)) G :=
    hShape.preservesLimit
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ equalizer.lift (FrobeniusSplitting.RetainedCharacter.coordinateProduct N
        cG G f) _ ≫ z)
      (PreservesEqualizer.iso_inv_ι G (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
        (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n))).trans
            (equalizer.lift_ι _ _))

/-- Each original coordinate of the factored map is the specified one. -/
theorem mappedLift_coordinate {P : D}
    (f : ∀ j, P ⟶ G.obj (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG j))
    (hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s j hj))) =
        f k ≫ G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsMap cG.pt.left
          (FrobeniusSplitting.RetainedCharacter.nodeMap N cG
              (FrobeniusSplitting.RetainedCharacter.liftArrow s k hk))) ≫
          G.map (FrobeniusSplitting.CharacterLine.relativeFunctionsSmul cG.pt.left
              (FrobeniusSplitting.RetainedCharacter.node N cG s)
            ((Scheme.ΓSpecIso (.of (N.obj s))).inv
              ((delta₀ s j hj k hk : N.obj s) ^ n)))) (j : J) :
    FrobeniusSplitting.RetainedCharacter.mappedLift N cG delta₀ n G f hf ≫ G.map
        (FrobeniusSplitting.RetainedCharacter.coordinate N cG delta₀ n j) = f j := by
  let l := FrobeniusSplitting.RetainedCharacter.mappedLift N cG delta₀ n G f hf
  let i := equalizer.ι (FrobeniusSplitting.RetainedCharacter.matchingFirst N cG)
      (FrobeniusSplitting.RetainedCharacter.matchingSecond N cG delta₀ n)
  let p := Pi.π (FrobeniusSplitting.RetainedCharacter.liftFunctions N cG) j
  change l ≫ G.map (i ≫ p) = f j
  calc
    l ≫ G.map (i ≫ p) = l ≫ (G.map i ≫ G.map p) := congrArg (fun z ↦ l ≫ z) (G.map_comp i p)
    _ = (l ≫ G.map i) ≫ G.map p := (Category.assoc _ _ _).symm
    _ = FrobeniusSplitting.RetainedCharacter.coordinateProduct N cG G f ≫ G.map p :=
      congrArg (fun z ↦ z ≫ G.map p) (FrobeniusSplitting.RetainedCharacter.mappedLift_inclusion N
          cG delta₀ n G f hf)
    _ = f j := FrobeniusSplitting.RetainedCharacter.coordinateProduct_projection N cG G f j

end FrobeniusSplitting.RetainedCharacter
