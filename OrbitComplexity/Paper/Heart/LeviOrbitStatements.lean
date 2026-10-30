import OrbitComplexity.Paper.Heart.LeviCodimension
import OrbitComplexity.Paper.Heart.LeviSurjection
import OrbitComplexity.Paper.Heart.ComplementEquivalences

/-! # Orbit correspondences from Schubert cells

Torus orbits of the heart, and of the minimal parabolic cell, map onto Levi--Borel
orbits of the original cell. When the Levi acts on the Schubert variety these maps
are bijections preserving integer orbit codimension.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem root_descents_of_action (I : Set G.rootBase.support) (w : G.weylGroup)
    (hact : ∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
      letI := a
      IsModHom (leviVariety G I).toOver (schubertInclusion G w)) :
    ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i) := by
  have hdesc := (levi_schubert_action_iff G I w).mp hact
  have ha := (complement_equivalences G I w).2.2.2.mp hdesc
  exact (leftFactor_longest_iff G.rootBase I w).2.mp ha

/-- Heart torus orbits surject onto cell Levi--Borel orbits, bijectively preserving codimension
when the standard Levi acts on the Schubert variety. -/
theorem heart_levi_orbits (I : Set G.rootBase.support) (w : G.weylGroup) :
    ∃ f : MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points →
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points,
      (∀ h : (heart G I w).points,
        f ⟦h⟧ = ⟦Variety.mapPoints (heartCellInclusion G I w) h⟧) ∧
      Function.Surjective f ∧
      ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) →
        Function.Bijective f ∧ ∀ h : (heart G I w).points,
          orbitCodim (leviBorelVariety G I) (schubertCell G w)
              (Variety.mapPoints (heartCellInclusion G I w) h) =
            orbitCodim (torusVariety G) (heart G I w) h) := by
  refine ⟨heartLeviOrbitMap G I w, heartLeviOrbitMap_mk G I w,
    heartLeviOrbitMap_surjective G I w, ?_⟩
  intro hact
  have hI := root_descents_of_action G I w hact
  have he : heartLeviOrbitMap G I w = heartLeviOrbitEquiv G I w hI := by
    funext q
    induction q using Quotient.inductionOn with
    | h h => rfl
  refine ⟨?_, heartLeviOrbitCodim G I w hI⟩
  rw [he]
  exact (heartLeviOrbitEquiv G I w hI).bijective

/-- Parabolic translation gives a surjection from minimal-cell torus orbits to Levi--Borel
cell orbits, and an orbit codimension preserving bijection when the Levi acts. -/
theorem torus_levi_orbits (I : Set G.rootBase.support) (w : G.weylGroup) :
    let d := leftParabolicRepresentative G.rootBase I w
    let p := (heartTranslationIso G I w).hom ≫ heartCellInclusion G I w
    ∃ f : MulAction.orbitRel.Quotient (torusVariety G).points (schubertCell G d).points →
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points,
      (∀ x : (schubertCell G d).points,
        f ⟦x⟧ = ⟦Variety.mapPoints p x⟧ ∧
        Variety.mapPoints (schubertCellInclusion G w) (Variety.mapPoints p x) =
          reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)) •
            Variety.mapPoints (schubertCellInclusion G d) x) ∧
      Function.Surjective f ∧
      ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) →
        Function.Bijective f ∧ ∀ x : (schubertCell G d).points,
          orbitCodim (leviBorelVariety G I) (schubertCell G w) (Variety.mapPoints p x) =
            orbitCodim (torusVariety G) (schubertCell G d) x) := by
  dsimp only
  refine ⟨cellLeviOrbitMap G I w, ?_, cellLeviOrbitMap_surjective G I w, ?_⟩
  · intro x
    constructor
    · rw [Variety.mapPoints_comp]
      exact cellLeviOrbitMap_mk G I w x
    · rw [Variety.mapPoints_comp, ← Variety.mapPoints_comp, heartCellInclusion_comp]
      exact heartTranslationIso_points G I w x
  · intro hact
    have hI := root_descents_of_action G I w hact
    have he : cellLeviOrbitMap G I w = cellLeviOrbitEquiv G I w hI := by
      funext q
      induction q using Quotient.inductionOn with
      | h h => rfl
    refine ⟨?_, ?_⟩
    · rw [he]
      exact (cellLeviOrbitEquiv G I w hI).bijective
    · intro x
      rw [Variety.mapPoints_comp]
      exact cellLeviOrbitCodim G I w hI x

/-- The heart orbit correspondence over the complex numbers. -/
theorem heart_levi_orbits_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    ∃ f : MulAction.orbitRel.Quotient (torusVariety G).points (heart G I w).points →
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points,
      (∀ h : (heart G I w).points,
        f ⟦h⟧ = ⟦Variety.mapPoints (heartCellInclusion G I w) h⟧) ∧
      Function.Surjective f ∧
      ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) →
        Function.Bijective f ∧ ∀ h : (heart G I w).points,
          orbitCodim (leviBorelVariety G I) (schubertCell G w)
              (Variety.mapPoints (heartCellInclusion G I w) h) =
            orbitCodim (torusVariety G) (heart G I w) h) :=
  heart_levi_orbits G I w

/-- The translated minimal-cell orbit correspondence over the complex numbers. -/
theorem torus_levi_orbits_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup) :
    let d := leftParabolicRepresentative G.rootBase I w
    let p := (heartTranslationIso G I w).hom ≫ heartCellInclusion G I w
    ∃ f : MulAction.orbitRel.Quotient (torusVariety G).points (schubertCell G d).points →
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G w).points,
      (∀ x : (schubertCell G d).points,
        f ⟦x⟧ = ⟦Variety.mapPoints p x⟧ ∧
        Variety.mapPoints (schubertCellInclusion G w) (Variety.mapPoints p x) =
          reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)) •
            Variety.mapPoints (schubertCellInclusion G d) x) ∧
      Function.Surjective f ∧
      ((∃ a : ModObj (leviVariety G I).toOver (schubertVariety G w).toOver,
        letI := a
        IsModHom (leviVariety G I).toOver (schubertInclusion G w)) →
        Function.Bijective f ∧ ∀ x : (schubertCell G d).points,
          orbitCodim (leviBorelVariety G I) (schubertCell G w) (Variety.mapPoints p x) =
            orbitCodim (torusVariety G) (schubertCell G d) x) :=
  torus_levi_orbits G I w

end SchubertOrbits
