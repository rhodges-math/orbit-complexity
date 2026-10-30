import OrbitComplexity.SchubertGeometry.ProjectiveLine.RadicalAction

/-! # The Borel action through a singleton Levi Borel -/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem levi_le_parabolic (I : Set G.rootBase.support) :
    G.leviPoints I ≤ standardParabolicPoints G I := by
  rw [parabolic_eq_levi_sup_unipotent]
  exact le_sup_left

private theorem borelFlag_raw (b : (borelVariety G).points) (q : (flagVariety G).points) :
    b • q = reductivePointsMulEquiv G (borelPointsMulEquiv G b) • q := by
  obtain ⟨x, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
  rw [borelFlag_smul, flagVarietyAction_points]

private theorem borel_factor (i : G.rootBase.support) (b : (borelVariety G).points) :
    ∃ r : G.points, r ∈ parabolicUnipotentPoints G {i} ∧
      (borelPointsMulEquiv G b : G.points) =
        (leviBorelPointsMulEquiv G {i} (Variety.mapPoints (simpleBorelProjection G i) b) :
          G.points) * r := by
  let p := parabolicPointsMulEquiv G {i}
    (Variety.mapPoints (borelParabolicInclusion G {i}) b)
  let l := leviBorelPointsMulEquiv G {i} (Variety.mapPoints (simpleBorelProjection G i) b)
  let ll : G.leviPoints {i} := ⟨l.val, l.property.1⟩
  let lp : standardParabolicPoints G {i} := ⟨l.val, levi_le_parabolic G {i} l.property.1⟩
  have hbproj : parabolicPointProjection G {i} p = ll :=
    Subtype.ext (simpleBorelProjection_points G i b).symm
  have hlproj : parabolicPointProjection G {i} lp = ll :=
    parabolicPointProjection_levi G {i} ll
  let r : standardParabolicPoints G {i} := lp⁻¹ * p
  have hrker : r ∈ (parabolicPointProjection G {i}).ker := by
    change parabolicPointProjection G {i} (lp⁻¹ * p) = 1
    rw [map_mul, map_inv, hlproj, hbproj, inv_mul_cancel]
  have hr : (r : G.points) ∈ parabolicUnipotentPoints G {i} := by
    rw [parabolicPointProjection_ker] at hrker
    exact hrker
  have he : (borelPointsMulEquiv G b : G.points) = (l : G.points) * (r : G.points) := by
    have hb : (p : G.points) = (borelPointsMulEquiv G b : G.points) :=
      borelParabolic_points G {i} b
    rw [← hb]
    change (p : G.points) = (lp : G.points) * ((lp : G.points)⁻¹ * (p : G.points))
    group
  exact ⟨r, hr, he⟩

private theorem smul_map_factor {A B Q : Type*} [Group A] [Group B] [MulAction B Q]
    (f : A →* B) (a l r : A) (q : Q) (he : a = l * r) (hr : f r • q = q) :
    f a • q = f l • q := by
  rw [he, map_mul, mul_smul, hr]

/-- Borel translation of a simple-Schubert flag depends on its singleton Levi projection. -/
theorem simpleBorelProjection_flag_smul (i : G.rootBase.support)
    (b : (borelVariety G).points)
    (q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    reductivePointsMulEquiv G (borelPointsMulEquiv G b) •
        Variety.mapPoints
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q =
      reductivePointsMulEquiv G
        (leviBorelPointsMulEquiv G {i} (Variety.mapPoints (simpleBorelProjection G i) b)) •
        Variety.mapPoints
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q := by
  obtain ⟨r, hr, he⟩ := borel_factor G i b
  exact smul_map_factor (reductivePointsMulEquiv G).toMonoidHom _ _ r _ he
    (simpleRadical_flag_fixed G i r hr q)

private theorem projectedFlag_action (i : G.rootBase.support)
    (b : (borelVariety G).points)
    (q : (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).points) :
    type_of% ((borelFlag_raw G b
      (Variety.mapPoints
        (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q)).trans
      ((simpleBorelProjection_flag_smul G i b q).trans
        (leviBorelFlag_smul G {i} (Variety.mapPoints (simpleBorelProjection G i) b)
          (Variety.mapPoints
            (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q)).symm)) :=
  (borelFlag_raw G b
    (Variety.mapPoints
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q)).trans
    ((simpleBorelProjection_flag_smul G i b q).trans
      (leviBorelFlag_smul G {i} (Variety.mapPoints (simpleBorelProjection G i) b)
        (Variety.mapPoints
          (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) q)).symm)

/-- The singleton Levi-Borel projection gives the Borel action on its simple Schubert variety. -/
@[instance_reducible] def simpleBorelAction (i : G.rootBase.support) :
    ModObj (borelVariety G).toOver
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver :=
  Mod.scalarRestriction (simpleBorelProjection G i)
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver

/-- The singleton-projected Borel action agrees with multiplication on the flag variety. -/
theorem simpleBorelAction_equivariant (i : G.rootBase.support) :
    letI := simpleBorelAction G i
    IsModHom (borelVariety G).toOver
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) := by
  let := simpleBorelAction G i
  apply Variety.isModHom_of_points
  intro b q
  have hs := Variety.restricted_smul (simpleBorelProjection G i)
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) b q
  exact (congrArg (Variety.mapPoints
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) hs).trans
      ((leviBorelSchubert_smul G {i}
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
        (Variety.mapPoints (simpleBorelProjection G i) b) q).trans
          (projectedFlag_action G i b q).symm)

end SchubertGeometry
