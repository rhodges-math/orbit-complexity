import OrbitComplexity.Paper.Heart.TwistedComplex
import OrbitComplexity.SchubertGeometry.Cells.Actions

/-! # Twisted torus actions on Schubert cells

Weyl conjugation defines representative-independent torus actions. Their orbits agree with
ordinary torus orbits on every torus variety, including each Schubert cell.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory
universe u

/-- Weyl twists preserve all torus and Schubert-cell orbits, independently of representatives. -/
theorem twistedActions_schubert {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)
    (u : G.weylGroup) (X : Variety K)
    [ModObj (torusVariety G).toOver X.toOver] :
    (∀ s : G.torusPoints,
      (torusConjugationIso G (G.weylPoint u * s)
        (Subgroup.mul_mem _ (G.weylPoint_mem_normalizer u)
          (G.torusPoints.le_normalizer s.property))).hom =
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom) ∧
    (∀ (t : (torusVariety G).points) (x : X.points),
      let ordinarySmul : (torusVariety G).points → X.points → X.points := (· • ·)
      letI := twistedAction G u X
      t • x = ordinarySmul (Variety.mapPoints
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom t) x) ∧
    (∀ x : X.points,
      let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
      letI := twistedAction G u X
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit) ∧
    (let ordinaryOpenDense := (∃ x : X.points,
       IsOpen (MulAction.orbit (torusVariety G).points x) ∧
         Dense (MulAction.orbit (torusVariety G).points x));
      letI := twistedAction G u X;
      (∃ x : X.points, IsOpen (MulAction.orbit (torusVariety G).points x) ∧
        Dense (MulAction.orbit (torusVariety G).points x)) ↔ ordinaryOpenDense) ∧
    (∀ (d : G.weylGroup) (x : (schubertCell G d).points),
      let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
      letI := twistedAction G u (schubertCell G d)
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit) := by
  obtain ⟨hr, hs, ho, hd⟩ := twistedAction_properties G u X
  exact ⟨hr, hs, ho, hd, fun d x => twistedAction_orbit G u (schubertCell G d) x⟩

/-- Representative independence and equality of ordinary and twisted Schubert-cell orbits over ℂ. -/
theorem twistedActions_schubert_complex (G : ReductiveGroupData ℂ)
    (u : G.weylGroup) (X : Variety ℂ)
    [ModObj (torusVariety G).toOver X.toOver] :
    (∀ s : G.torusPoints,
      (torusConjugationIso G (G.weylPoint u * s)
        (Subgroup.mul_mem _ (G.weylPoint_mem_normalizer u)
          (G.torusPoints.le_normalizer s.property))).hom =
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom) ∧
    (∀ (t : (torusVariety G).points) (x : X.points),
      let ordinarySmul : (torusVariety G).points → X.points → X.points := (· • ·)
      letI := twistedAction G u X
      t • x = ordinarySmul (Variety.mapPoints
        (torusConjugationIso G (G.weylPoint u) (G.weylPoint_mem_normalizer u)).hom t) x) ∧
    (∀ x : X.points,
      let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
      letI := twistedAction G u X
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit) ∧
    (let ordinaryOpenDense := (∃ x : X.points,
       IsOpen (MulAction.orbit (torusVariety G).points x) ∧
         Dense (MulAction.orbit (torusVariety G).points x));
      letI := twistedAction G u X;
      (∃ x : X.points, IsOpen (MulAction.orbit (torusVariety G).points x) ∧
        Dense (MulAction.orbit (torusVariety G).points x)) ↔ ordinaryOpenDense) ∧
    (∀ (d : G.weylGroup) (x : (schubertCell G d).points),
      let ordinaryOrbit := MulAction.orbit (torusVariety G).points x
      letI := twistedAction G u (schubertCell G d)
      MulAction.orbit (torusVariety G).points x = ordinaryOrbit) :=
  twistedActions_schubert G u X

end SchubertOrbits
