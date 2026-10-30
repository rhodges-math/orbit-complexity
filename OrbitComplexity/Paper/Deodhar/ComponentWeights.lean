import OrbitComplexity.SchubertGeometry.Deodhar.ComponentIsomorphisms
import OrbitComplexity.Paper.Deodhar.ParameterMaps
import OrbitComplexity.Paper.Deodhar.ComponentOrbitDimensions
import OrbitComplexity.Paper.Deodhar.OrbitWeights
import OrbitComplexity.Paper.Deodhar.MaximalWeights
import OrbitComplexity.BruhatIntervals.Words.Subword
import OrbitComplexity.GroupActions.Actions.OrbitIso

/-! # Weights on intrinsic Deodhar components

The inverse parameter chart gives the general locus and the active root weights.
The equivariant component chart identifies their spans and torus orbit dimensions.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open ReductiveGroups BruhatIntervals SchubertGeometry
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
attribute [local irreducible] deodharParameters deodharComponentIso

/-- General component points have nonzero coordinates in the inverse parameter chart. -/
def deodharGeneralPoints : Set (deodharComponent G expression hred).points :=
  mapPoints (X := deodharComponent G expression hred) (Y := deodharParameters G expression)
    (deodharComponentIso G expression hred hd).inv ⁻¹'
      deodharGeneralParameters G expression

/-- The component orbit weights are the active negative roots in its parameter chart. -/
def deodharComponentWeightSpan (x : (deodharComponent G expression hred).points) :
    Submodule ℝ (G.rootBase.support →₀ ℝ) :=
  deodharOrbitWeightSpan G expression
    (mapPoints (X := deodharComponent G expression hred) (Y := deodharParameters G expression)
      (deodharComponentIso G expression hred hd).inv x)

private theorem componentIso_equivariant :
    letI := deodharParameterAction G expression
    IsModHom (torusVariety G).toOver (deodharComponentIso G expression hred hd).hom := by
  let := deodharParameterAction G expression
  have : IsModHom (torusVariety G).toOver
      (deodharPrefixMorphism G expression word.length) :=
    deodharPrefixMorphism_isModHom G expression word.length
  have : Mono (deodharInclusion G expression hred).left := by
    change Mono ((deodharPrefixInclusion G expression hred word.length).left ≫
      (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take word.length))).left)
    infer_instance
  have : Mono (deodharInclusion G expression hred) :=
    Over.mono_of_mono_left (deodharInclusion G expression hred)
  constructor
  apply (cancel_mono (deodharInclusion G expression hred)).mp
  rw [Category.assoc, deodharComponentIso_flag, IsModHom.smul_hom]
  rw [Category.assoc, IsModHom.smul_hom, ← Category.assoc,
    ← MonoidalCategory.MonoidalLeftAction.actionHomRight_comp, deodharComponentIso_flag]

private theorem component_general_properties :
    (∀ x : (deodharComponent G expression hred).points,
      x ∈ deodharGeneralPoints G expression hred hd ↔
        ∀ j : deodharIndex G expression,
          j.down.val ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (X := deodharParameters G expression)
              (Y := affineSpaceVariety K (deodharIndex G expression))
              (deodharParameterInclusion G expression)
              (mapPoints (X := deodharComponent G expression hred)
                (Y := deodharParameters G expression)
                (deodharComponentIso G expression hred hd).inv x)) j ≠ 0) ∧
    IsOpen (deodharGeneralPoints G expression hred hd) ∧
    Dense (deodharGeneralPoints G expression hred hd) ∧
    (deodharGeneralPoints G expression hred hd).Nonempty := by
  let h := pointsHomeomorph (X := deodharParameters G expression)
    (Y := deodharComponent G expression hred) (deodharComponentIso G expression hred hd)
  have hg := deodharGeneral_properties G expression
  have hopen : IsOpen (deodharGeneralPoints G expression hred hd) :=
    hg.2.1.preimage (continuous_mapPoints (X := deodharComponent G expression hred)
      (Y := deodharParameters G expression) (deodharComponentIso G expression hred hd).inv)
  have hnonempty : (deodharGeneralPoints G expression hred hd).Nonempty := by
    obtain ⟨x, hx⟩ := hg.2.2.2.1
    refine ⟨h x, ?_⟩
    change h.symm (h x) ∈ deodharGeneralParameters G expression
    simpa only [h.symm_apply_apply] using hx
  have : IrreducibleSpace (deodharComponent G expression hred).points :=
    h.irreducibleSpace_iff.mp inferInstance
  refine ⟨?_, hopen, hopen.dense hnonempty, hnonempty⟩
  intro x
  exact hg.1 (h.symm x)

private theorem component_orbit_weightSpan (x : (deodharComponent G expression hred).points) :
    orbitNatDim (torusVariety G) (deodharComponent G expression hred) x =
      Module.finrank ℝ (deodharComponentWeightSpan G expression hred hd x) := by
  let := deodharParameterAction G expression
  have : IsModHom (torusVariety G).toOver (deodharComponentIso G expression hred hd).hom :=
    componentIso_equivariant G expression hred hd
  let h := pointsHomeomorph (X := deodharParameters G expression)
    (Y := deodharComponent G expression hred) (deodharComponentIso G expression hred hd)
  calc
    _ = orbitNatDim (torusVariety G) (deodharComponent G expression hred) (h (h.symm x)) :=
      congrArg (orbitNatDim (torusVariety G) (deodharComponent G expression hred))
        (h.apply_symm_apply x).symm
    _ = orbitNatDim (torusVariety G) (deodharParameters G expression) (h.symm x) :=
      orbitNatDim_iso (torusVariety G) (X := deodharParameters G expression)
        (Y := deodharComponent G expression hred) (deodharComponentIso G expression hred hd)
        (h.symm x)
    _ = _ := deodharParameter_orbit_weightSpan G expression (h.symm x)

/-- Component orbit weights lie in the subword span, general points attain it, the positive
distinguished span is the interval label span, and each parameter coordinate scales by the torus
character of its weight. -/
theorem deodharComponent_weights :
    (letI := deodharParameterAction G expression
     IsModHom (torusVariety G).toOver (deodharComponentIso G expression hred hd).hom) ∧
    (∀ x : (deodharComponent G expression hred).points,
      x ∈ deodharGeneralPoints G expression hred hd ↔
        ∀ j : deodharIndex G expression,
          j.down.val ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (X := deodharParameters G expression)
              (Y := affineSpaceVariety K (deodharIndex G expression))
              (deodharParameterInclusion G expression)
              (mapPoints (X := deodharComponent G expression hred)
                (Y := deodharParameters G expression)
                (deodharComponentIso G expression hred hd).inv x)) j ≠ 0) ∧
    IsOpen (deodharGeneralPoints G expression hred hd) ∧
    Dense (deodharGeneralPoints G expression hred hd) ∧
    (deodharGeneralPoints G expression hred hd).Nonempty ∧
    (∀ x : (deodharComponent G expression hred).points,
      deodharComponentWeightSpan G expression hred hd x ≤
        subwordWeightSpan (weylRealization G.rootBase) expression) ∧
    (∀ x ∈ deodharGeneralPoints G expression hred hd,
      deodharComponentWeightSpan G expression hred hd x =
        subwordWeightSpan (weylRealization G.rootBase) expression) ∧
    (∀ x : (deodharComponent G expression hred).points,
      orbitNatDim (torusVariety G) (deodharComponent G expression hred) x =
        Module.finrank ℝ (deodharComponentWeightSpan G expression hred hd x)) ∧
    (∃ positive : Subexpression word,
      positive.prefixProd (weylCoxeterSystem G.rootBase) word.length =
        expression.prefixProd (weylCoxeterSystem G.rootBase) word.length ∧
      IsDistinguished (weylCoxeterSystem G.rootBase) positive ∧
      IsPositive (weylCoxeterSystem G.rootBase) positive ∧
      subwordWeightSpan (weylRealization G.rootBase) expression ≤
        subwordWeightSpan (weylRealization G.rootBase) positive ∧
      subwordWeightSpan (weylRealization G.rootBase) positive =
        labelSpan (weylRealization G.rootBase)
          (expression.prefixProd (weylCoxeterSystem G.rootBase) word.length)
          ((weylCoxeterSystem G.rootBase).wordProd word)) ∧
    (letI := deodharParameterAction G expression
     ∀ (t : (torusVariety G).points) (x : (deodharParameters G expression).points)
       (j : deodharIndex G expression),
       affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
           (mapPoints (deodharParameterInclusion G expression) (t • x)) j =
         affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
             (mapPoints (deodharParameterInclusion G expression) x) j *
           affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm
             (MonoidAlgebra.single (subwordCharacter G expression j.down) 1))) := by
  have hg := component_general_properties G expression hred hd
  refine ⟨componentIso_equivariant G expression hred hd, hg.1, hg.2.1, hg.2.2.1,
    hg.2.2.2, ?_, ?_, component_orbit_weightSpan G expression hred hd, ?_,
    fun t x j => deodharParameter_smul G expression t x j⟩
  · intro x
    exact deodharOrbitWeightSpan_le G expression _
  · intro x hx
    exact deodharGeneral_weightSpan G expression _ hx
  · have hle := (subexpression_subword_property (weylCoxeterSystem G.rootBase) hred
      (w := (weylCoxeterSystem G.rootBase).wordProd word) rfl).mpr ⟨expression, rfl⟩
    obtain ⟨positive, hp, _⟩ := positive_subwordWeightSpan (weylRealization G.rootBase)
      hred _ hle
    refine ⟨positive, hp.1, hp.2.1, hp.2.2.1, ?_, hp.2.2.2.1⟩
    rw [hp.2.2.2.1]
    exact (subwordWeightSpan_interval (weylRealization G.rootBase) expression hred hd).1

include hd in
/-- A component torus orbit is bounded by its subexpression weight dimension. -/
theorem deodharComponent_orbit_le (y : (deodharComponent G expression hred).points) :
    orbitNatDim (torusVariety G) (deodharComponent G expression hred) y ≤
      subwordWeightDim (weylRealization G.rootBase) expression := by
  obtain ⟨_, _, _, _, _, hspan, _, hrank, _⟩ :=
    deodharComponent_weights G expression hred hd
  exact (hrank y).le.trans (Submodule.finrank_mono (hspan y))

include hd in
/-- A component has a torus orbit of its subexpression weight dimension. -/
theorem deodharComponent_orbit_attains :
    ∃ y : (deodharComponent G expression hred).points,
      orbitNatDim (torusVariety G) (deodharComponent G expression hred) y =
        subwordWeightDim (weylRealization G.rootBase) expression := by
  obtain ⟨_, _, _, _, hnonempty, _, hgeneral, hrank, _⟩ :=
    deodharComponent_weights G expression hred hd
  obtain ⟨y, hy⟩ := hnonempty
  exact ⟨y, (hrank y).trans (congrArg
    (fun V : Submodule ℝ (G.rootBase.support →₀ ℝ) => Module.finrank ℝ V)
      (hgeneral y hy))⟩

end
end SchubertOrbits
