import OrbitComplexity.GroupActions.Rosenlicht.InvariantFibres
import OrbitComplexity.GroupActions.Actions.OpenSaturation
import OrbitComplexity.GroupActions.Rosenlicht.InvariantTranslations

/-!
# Orbit fibres on a stable open subset

Saturating a generic separating open subset gives a stable open on which the invariant
morphism separates the group orbits.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

omit [IsAlgClosed K] [IrreducibleSpace H.scheme] in
private theorem invariantMorphism_smul (h : H.points) (x : X.points)
    (hx : X.pointMap x ∈ (invariantMap H X).domain)
    (htx : X.pointMap (h • x) ∈ (invariantMap H X).domain) :
    (invariantMorphism H X).left ⟨X.pointMap (h • x), htx⟩ =
      (invariantMorphism H X).left ⟨X.pointMap x, hx⟩ := by
  have he : (translateMorphism H X h).left (X.pointMap x) = X.pointMap (h • x) := by
    rw [← pointMap_mapPoints, mapPoints_translateMorphism]
  have hh : (translateMorphism H X h).left (X.pointMap x) ∈ (invariantMap H X).domain := by
    rw [he]
    exact htx
  simpa only [he] using invariantMorphism_translate H X h (X.pointMap x) hx hh

/-- Saturating a separating open subset produces an invariant open domain
whose invariant-morphism fibres are precisely the group orbits. -/
theorem exists_saturated_invariant_fibres :
    ∃ U : X.scheme.Opens, (U : Set X.scheme).Nonempty ∧
      ∃ hUD : saturationOpen H X U ≤ (invariantMap H X).domain,
        ∀ (x y : X.points) (hx : X.pointMap x ∈ saturationOpen H X U)
          (hy : X.pointMap y ∈ saturationOpen H X U),
          (invariantMorphism H X).left ⟨X.pointMap x, hUD hx⟩ =
            (invariantMorphism H X).left ⟨X.pointMap y, hUD hy⟩ ↔
              y ∈ MulAction.orbit H.points x := by
  obtain ⟨U, hU, hUD, hsep⟩ := exists_open_invariantMap_fibres H X
  have hSD : saturationOpen H X U ≤ (invariantMap H X).domain :=
    saturationOpen_le H X U _ hUD (invariantMap_domain_translate H X)
  refine ⟨U, hU, hSD, ?_⟩
  intro x y hx hy
  constructor
  · intro hxy
    obtain ⟨g, hg⟩ := (mem_saturationOpen H X U x).mp hx
    obtain ⟨h, hh⟩ := (mem_saturationOpen H X U y).mp hy
    have hge := invariantMorphism_smul H X g x (hSD hx) (hUD hg)
    have hhe := invariantMorphism_smul H X h y (hSD hy) (hUD hh)
    have horbit := hsep (g • x) (h • y) hg hh (hge.trans (hxy.trans hhe.symm))
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp horbit
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h⁻¹ * a * g, ?_⟩
    calc
      (h⁻¹ * a * g) • x = h⁻¹ • (a • (g • x)) := by rw [mul_smul, mul_smul]
      _ = h⁻¹ • (h • y) := congrArg (fun z : X.points ↦ h⁻¹ • z) ha
      _ = y := inv_smul_smul h y
  · intro hxy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hxy
    exact (invariantMorphism_smul H X g x (hSD hx) (hSD hy)).symm

end

end GroupActions.Variety
