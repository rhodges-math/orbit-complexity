import OrbitComplexity.SchubertGeometry.Levi.BorelInclusion
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension

/-! # Levi--Borel orbits under restriction

Restricting an equivariant Levi action through the closed Borel inclusion gives
the established Schubert-variety orbits, integer codimensions and their minimum.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
  (I : Set G.rootBase.support) (w : G.weylGroup)
  [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
  [IsModHom (leviVariety G I).toOver (schubertInclusion G w)]

/-- Restricting an equivariant Levi action gives the established Levi--Borel orbits. -/
theorem leviBorel_restricted_orbit (q : (schubertVariety G w).points) :
    let ordinary := MulAction.orbit (leviBorelVariety G I).points q
    letI := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
    MulAction.orbit (leviBorelVariety G I).points q = ordinary := by
  let ordinarySmul : (leviBorelVariety G I).points → (schubertVariety G w).points →
      (schubertVariety G w).points := (· • ·)
  have hsmul (b : (leviBorelVariety G I).points) :
      Variety.mapPoints (leviBorelLeviInclusion G I) b • q = ordinarySmul b q :=
    leviBorelLevi_schubert_smul G I w b q
  let := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
  change Set.range (fun b : (leviBorelVariety G I).points => b • q) =
    Set.range (fun b : (leviBorelVariety G I).points => ordinarySmul b q)
  congr 1
  funext b
  exact (Variety.restricted_smul (leviBorelLeviInclusion G I) (schubertVariety G w) b q).trans
    (hsmul b)

/-- Restricting a Levi action to its Borel preserves the established integer codimensions. -/
theorem leviBorel_restricted_orbitCodim (q : (schubertVariety G w).points) :
    let ordinary := orbitCodim (leviBorelVariety G I) (schubertVariety G w) q
    letI := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
    orbitCodim (leviBorelVariety G I) (schubertVariety G w) q = ordinary := by
  let := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
  unfold orbitCodim orbitNatDim orbitDim
  rw [leviBorel_restricted_orbit G I w q]

/-- The minimum Borel orbit codimension agrees with restriction of any equivariant Levi action. -/
theorem leviBorel_restricted_minOrbitCodim :
    let ordinary := minOrbitCodim (leviBorelVariety G I) (schubertVariety G w)
    letI := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
    minOrbitCodim (leviBorelVariety G I) (schubertVariety G w) = ordinary := by
  let ordinaryCodim := orbitCodim (leviBorelVariety G I) (schubertVariety G w)
  have h :
      letI := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
      orbitCodim (leviBorelVariety G I) (schubertVariety G w) = ordinaryCodim := by
    let := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
    exact funext (leviBorel_restricted_orbitCodim G I w)
  let := Mod.scalarRestriction (leviBorelLeviInclusion G I) (schubertVariety G w).toOver
  unfold minOrbitCodim
  rw [h]

end SchubertGeometry
