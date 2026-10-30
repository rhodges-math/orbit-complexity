import OrbitComplexity.Paper.Heart.TwistedActions
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex twisted torus actions

The full twisted-action statement holds over every algebraically closed field of
characteristic zero and, in particular, over the complex numbers.

-/

noncomputable section

namespace SchubertOrbits

open ReductiveGroups GroupActions CategoryTheory

universe u

example {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (u : G.weylGroup) (X : Variety K)
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
        Dense (MulAction.orbit (torusVariety G).points x)) ↔ ordinaryOpenDense) :=
  twistedAction_properties G u X

end SchubertOrbits
