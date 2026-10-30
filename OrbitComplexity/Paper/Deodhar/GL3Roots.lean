import OrbitComplexity.ReductiveGroups.GLn.RootCoordinates
import OrbitComplexity.Paper.Deodhar.ParameterOrbits
import OrbitComplexity.Paper.Deodhar.ComponentWeights
import OrbitComplexity.Paper.Deodhar.ComponentOrbitDimensions
import OrbitComplexity.Paper.Deodhar.Scaling
import OrbitComplexity.BruhatIntervals.Permutations.PositiveRoots
import OrbitComplexity.ReductiveGroups.GLn.GroupData
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import Mathlib.Tactic

/-! # Simple roots in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ)

/-- The root with character t₀t₁⁻¹ in rank three. -/
def root01 : (GLn.groupData K 3).rootIndex := matrixRoot 3 0 1 (by decide)

/-- The root with character t₁t₂⁻¹ in rank three. -/
def root12 : (GLn.groupData K 3).rootIndex := matrixRoot 3 1 2 (by decide)

/-- The root with character t₀t₂⁻¹ in rank three. -/
def root02 : (GLn.groupData K 3).rootIndex := matrixRoot 3 0 2 (by decide)

private theorem positive_cases (r : (GLn.groupData K 3).rootIndex)
    (hr : (GLn.groupData K 3).rootBase.IsPos r) :
    r = root01 ∨ r = root12 ∨ r = root02 := by
  obtain ⟨i, j, hij, hc⟩ := rootCharacter_pair 3 r
  have he : r = matrixRoot 3 i j hij := by
    apply (GLn.groupData K 3).characterRootEquiv.symm.injective
    apply Subtype.ext
    exact hc.trans (rootCharacter_matrixRoot 3 i j hij).symm
  subst r
  have hlt := (matrixRoot_positive 3 i j hij).mp hr
  rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 2) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem root_add_character (a b c : (GLn.groupData K 3).rootIndex)
    (h : (GLn.groupData K 3).rootSystem.root c =
      (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b) :
    ((GLn.groupData K 3).rootCharacter c).toAdd =
      ((GLn.groupData K 3).rootCharacter a).toAdd +
      ((GLn.groupData K 3).rootCharacter b).toAdd := by
  let G := GLn.groupData K 3
  have hs : G.rootSystem.rootSpanMem ℤ c =
      G.rootSystem.rootSpanMem ℤ a + G.rootSystem.rootSpanMem ℤ b := Subtype.ext h
  have hc := congrArg G.rootCharacterMap hs
  simpa only [map_add, G.rootCharacterMap_root] using hc

private def coordinates (r : (GLn.groupData K 3).rootIndex) : Fin 3 → ℤ :=
  fun x => ((GLn.groupData K 3).rootCharacter r).toAdd (ULift.up x)

private theorem coordinates_matrixRoot (i j : Fin 3) (hij : i ≠ j) (x : Fin 3) :
    coordinates (K := K) (matrixRoot (K := K) 3 i j hij) x =
      (if x = i then 1 else 0) - (if x = j then 1 else 0) := by
  unfold coordinates
  rw [rootCharacter_matrixRoot]
  change ((Finsupp.single (ULift.up i) (1 : ℤ) - Finsupp.single (ULift.up j) 1) :
    ULift.{u} (Fin 3) →₀ ℤ) (ULift.up x) = _
  simp only [Finsupp.sub_apply, Finsupp.single_apply, ULift.up_inj, eq_comm]

private theorem coordinates_add (a b c : (GLn.groupData K 3).rootIndex)
    (h : (GLn.groupData K 3).rootSystem.root c =
      (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b) :
    coordinates c = coordinates a + coordinates b := by
  have hc := root_add_character a b c h
  funext x
  exact congrArg (fun f : (GLn.groupData K 3).torusIndex →₀ ℤ => f (ULift.up x)) hc

private theorem no_positive_sum01 (a b : (GLn.groupData K 3).rootIndex)
    (ha : (GLn.groupData K 3).rootBase.IsPos a)
    (hb : (GLn.groupData K 3).rootBase.IsPos b) :
    (GLn.groupData K 3).rootSystem.root root01 ≠
      (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b := by
  intro h
  have hc := coordinates_add a b root01 h
  rcases positive_cases a ha with rfl | rfl | rfl <;>
    rcases positive_cases b hb with rfl | rfl | rfl
  all_goals
    have h0 := congrFun hc (0 : Fin 3)
    have h2 := congrFun hc (2 : Fin 3)
    norm_num [root01, root12, root02, coordinates_matrixRoot, Pi.add_apply] at h0 <;>
      norm_num [root01, root12, root02, coordinates_matrixRoot, Pi.add_apply] at h2

private theorem no_positive_sum12 (a b : (GLn.groupData K 3).rootIndex)
    (ha : (GLn.groupData K 3).rootBase.IsPos a)
    (hb : (GLn.groupData K 3).rootBase.IsPos b) :
    (GLn.groupData K 3).rootSystem.root root12 ≠
      (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b := by
  intro h
  have hc := coordinates_add a b root12 h
  rcases positive_cases a ha with rfl | rfl | rfl <;>
    rcases positive_cases b hb with rfl | rfl | rfl
  all_goals
    have h0 := congrFun hc (0 : Fin 3)
    have h1 := congrFun hc (1 : Fin 3)
    norm_num [root01, root12, root02, coordinates_matrixRoot, Pi.add_apply] at h0 <;>
      norm_num [root01, root12, root02, coordinates_matrixRoot, Pi.add_apply] at h1

private theorem simple_of_no_positive_sum (r : (GLn.groupData K 3).rootIndex)
    (hr : (GLn.groupData K 3).rootBase.IsPos r)
    (hno : ∀ a b, (GLn.groupData K 3).rootBase.IsPos a →
      (GLn.groupData K 3).rootBase.IsPos b →
      (GLn.groupData K 3).rootSystem.root r ≠
        (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b) :
    r ∈ (GLn.groupData K 3).rootBase.support := by
  let G := GLn.groupData K 3
  have hp : G.rootBase.IsPos r ∧ (r = r → r ∈ G.rootBase.support) := by
    apply hr.induction_on_add (p := fun i => G.rootBase.IsPos i ∧
      (i = r → r ∈ G.rootBase.support))
    · intro i hi
      exact ⟨G.rootBase.isPos_of_mem_support hi, fun he => he ▸ hi⟩
    · intro i j k hsum hi hj
      refine ⟨hi.1.add (G.rootBase.isPos_of_mem_support hj) hsum, ?_⟩
      intro hkr
      subst k
      exact False.elim (hno i j hi.1 (G.rootBase.isPos_of_mem_support hj) hsum)
  exact hp.2 rfl

/-- The first adjacent-coordinate root is simple. -/
theorem root01_simple : root01 (K := K) ∈ (GLn.groupData K 3).rootBase.support :=
  simple_of_no_positive_sum root01
    ((matrixRoot_positive 3 0 1 (by decide)).mpr (by decide)) no_positive_sum01

/-- The second adjacent-coordinate root is simple. -/
theorem root12_simple : root12 (K := K) ∈ (GLn.groupData K 3).rootBase.support :=
  simple_of_no_positive_sum root12
    ((matrixRoot_positive 3 1 2 (by decide)).mpr (by decide)) no_positive_sum12

private theorem character_add_root (a b c : (GLn.groupData K 3).rootIndex)
    (h : ((GLn.groupData K 3).rootCharacter c).toAdd =
      ((GLn.groupData K 3).rootCharacter a).toAdd +
      ((GLn.groupData K 3).rootCharacter b).toAdd) :
    (GLn.groupData K 3).rootSystem.root c =
      (GLn.groupData K 3).rootSystem.root a + (GLn.groupData K 3).rootSystem.root b := by
  let G := GLn.groupData K 3
  have hs : G.rootSystem.rootSpanMem ℤ c =
      G.rootSystem.rootSpanMem ℤ a + G.rootSystem.rootSpanMem ℤ b := by
    apply G.rootCharacterMap_injective
    simpa only [map_add, G.rootCharacterMap_root] using h
  exact congrArg Subtype.val hs

private theorem root02_sum :
    (GLn.groupData K 3).rootSystem.root root02 =
      (GLn.groupData K 3).rootSystem.root root01 +
      (GLn.groupData K 3).rootSystem.root root12 := by
  apply character_add_root
  simp only [root01, root12, root02, rootCharacter_matrixRoot, matrixUnitWeight]
  change Finsupp.single (ULift.up (0 : Fin 3)) (1 : ℤ) - Finsupp.single (ULift.up 2) 1 =
    (Finsupp.single (ULift.up 0) 1 - Finsupp.single (ULift.up 1) 1) +
      (Finsupp.single (ULift.up 1) 1 - Finsupp.single (ULift.up 2) 1)
  abel

private theorem root02_not_simple :
    root02 (K := K) ∉ (GLn.groupData K 3).rootBase.support := by
  intro h
  let G := GLn.groupData K 3
  have hh := G.rootBase.height_add (root02_sum (K := K))
  rw [G.rootBase.height_one_of_mem_support h,
    G.rootBase.height_one_of_mem_support root01_simple,
    G.rootBase.height_one_of_mem_support root12_simple] at hh
  norm_num at hh

private theorem simple_cases (r : (GLn.groupData K 3).rootIndex)
    (hr : r ∈ (GLn.groupData K 3).rootBase.support) : r = root01 ∨ r = root12 := by
  rcases positive_cases r ((GLn.groupData K 3).rootBase.isPos_of_mem_support hr) with
      h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (root02_not_simple (h ▸ hr))

private theorem no_root_difference01 (k : (GLn.groupData K 3).rootIndex) :
    (GLn.groupData K 3).rootSystem.root root12 ≠
      (GLn.groupData K 3).rootSystem.root root01 + (GLn.groupData K 3).rootSystem.root k := by
  intro h
  have hc := coordinates_add root01 k root12 h
  obtain ⟨i, j, hij, hk⟩ := rootCharacter_pair 3 k
  have he : k = matrixRoot 3 i j hij := by
    apply (GLn.groupData K 3).characterRootEquiv.symm.injective
    exact Subtype.ext (hk.trans (rootCharacter_matrixRoot 3 i j hij).symm)
  subst k
  fin_cases i <;> fin_cases j
  all_goals
    have h1 := congrFun hc (1 : Fin 3)
    norm_num [root01, root12, coordinates_matrixRoot, Pi.add_apply] at h1

private theorem no_root_difference12 (k : (GLn.groupData K 3).rootIndex) :
    (GLn.groupData K 3).rootSystem.root root01 ≠
      (GLn.groupData K 3).rootSystem.root root12 + (GLn.groupData K 3).rootSystem.root k := by
  intro h
  have hc := coordinates_add root12 k root01 h
  obtain ⟨i, j, hij, hk⟩ := rootCharacter_pair 3 k
  have he : k = matrixRoot 3 i j hij := by
    apply (GLn.groupData K 3).characterRootEquiv.symm.injective
    exact Subtype.ext (hk.trans (rootCharacter_matrixRoot 3 i j hij).symm)
  subst k
  fin_cases i <;> fin_cases j
  all_goals
    have h1 := congrFun hc (1 : Fin 3)
    norm_num [root01, root12, coordinates_matrixRoot, Pi.add_apply] at h1

private theorem root01_ne_root12 : root01 (K := K) ≠ root12 := by
  intro h
  have hc := congrArg (fun r => coordinates (K := K) r (0 : Fin 3)) h
  norm_num [root01, root12, coordinates_matrixRoot] at hc

/-- The first simple reflection sends the second simple root to their sum. -/
theorem reflection01_root12 :
    (GLn.groupData K 3).rootSystem.reflectionPerm root01 root12 = root02 := by
  let G := GLn.groupData K 3
  have hp := (G.rootBase.isPos_of_mem_support root12_simple).reflectionPerm
    root01_simple root01_ne_root12.symm
  rcases positive_cases _ hp with he | he | he
  · have hi := congrArg (G.rootSystem.reflectionPerm root01) he
    rw [G.rootSystem.reflectionPerm_self] at hi
    have hh := congrArg G.rootBase.height hi
    have hn := G.rootBase.height_reflectionPerm_self root01
    change G.rootBase.height (G.rootSystem.reflectionPerm root01 root01) =
      -G.rootBase.height root01 at hn
    rw [hn, G.rootBase.height_one_of_mem_support root01_simple,
      G.rootBase.height_one_of_mem_support root12_simple] at hh
    omega
  · have hs : G.rootSystem.root root12 = G.rootSystem.root root01 +
        G.rootSystem.root (G.rootSystem.reflectionPerm root01 root02) := by
      rw [G.rootSystem.root_reflectionPerm, root02_sum, map_add,
        G.rootSystem.reflection_apply_self, ← G.rootSystem.root_reflectionPerm, he]
      abel
    exact False.elim (no_root_difference01 _ hs)
  · exact he

/-- The second simple reflection sends the first simple root to their sum. -/
theorem reflection12_root01 :
    (GLn.groupData K 3).rootSystem.reflectionPerm root12 root01 = root02 := by
  let G := GLn.groupData K 3
  have hp := (G.rootBase.isPos_of_mem_support root01_simple).reflectionPerm
    root12_simple root01_ne_root12
  rcases positive_cases _ hp with he | he | he
  · have hs : G.rootSystem.root root01 = G.rootSystem.root root12 +
        G.rootSystem.root (G.rootSystem.reflectionPerm root12 root02) := by
      rw [G.rootSystem.root_reflectionPerm, root02_sum, map_add,
        ← G.rootSystem.root_reflectionPerm root12 root01, he,
        G.rootSystem.reflection_apply_self]
      abel
    exact False.elim (no_root_difference12 _ hs)
  · have hi := congrArg (G.rootSystem.reflectionPerm root12) he
    rw [G.rootSystem.reflectionPerm_self] at hi
    have hh := congrArg G.rootBase.height hi
    have hn := G.rootBase.height_reflectionPerm_self root12
    change G.rootBase.height (G.rootSystem.reflectionPerm root12 root12) =
      -G.rootBase.height root12 at hn
    rw [hn, G.rootBase.height_one_of_mem_support root01_simple,
      G.rootBase.height_one_of_mem_support root12_simple] at hh
    omega
  · exact he

/-- The first simple reflection sends the long coordinate root to the second root. -/
theorem reflection01_root02 :
    (GLn.groupData K 3).rootSystem.reflectionPerm root01 root02 = root12 := by
  rw [← reflection01_root12, (GLn.groupData K 3).rootSystem.reflectionPerm_self]

/-- The first adjacent-coordinate simple root. -/
def simple01 : (GLn.groupData K 3).rootBase.support := ⟨root01, root01_simple⟩

/-- The second adjacent-coordinate simple root. -/
def simple12 : (GLn.groupData K 3).rootBase.support := ⟨root12, root12_simple⟩

/-- Reflecting a matrix root in itself reverses its two indices. -/
theorem matrixRoot_swap (i j : Fin 3) (hij : i ≠ j) :
    (GLn.groupData K 3).rootSystem.reflectionPerm (matrixRoot 3 i j hij)
      (matrixRoot 3 i j hij) = matrixRoot 3 j i hij.symm := by
  let G := GLn.groupData K 3
  have hs : G.rootSystem.rootSpanMem ℤ
      (G.rootSystem.reflectionPerm (matrixRoot 3 i j hij) (matrixRoot 3 i j hij)) =
        G.rootSystem.rootSpanMem ℤ (matrixRoot 3 j i hij.symm) := by
    apply G.rootCharacterMap_injective
    rw [G.rootSystem.rootSpanMem_reflectionPerm_self, map_neg,
      G.rootCharacterMap_root, G.rootCharacterMap_root,
      rootCharacter_matrixRoot, rootCharacter_matrixRoot]
    change -(Finsupp.single (ULift.up i) (1 : ℤ) - Finsupp.single (ULift.up j) 1) =
      Finsupp.single (ULift.up j) 1 - Finsupp.single (ULift.up i) 1
    abel
  exact G.rootSystem.root.injective (congrArg Subtype.val hs)

end SchubertOrbits.GL3
