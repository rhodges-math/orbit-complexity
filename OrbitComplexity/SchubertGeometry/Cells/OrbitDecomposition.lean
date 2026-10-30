import OrbitComplexity.SchubertGeometry.Levi.Schubert
import OrbitComplexity.SchubertGeometry.Cells.Decomposition
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension
/-! # Levi--Borel orbits in the Bruhat decomposition

Every point of a Schubert variety lies in a unique lower Schubert cell.
The invariant cell inclusions identify its Levi--Borel orbit quotient with the
sum of the lower-cell orbit quotients, preserving their representatives.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions Topology ReductiveGroups
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
private theorem lower_points_cover (w : G.weylGroup) (q : (schubertVariety G w).points) :
    ∃ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      ∃ p : (schubertCell G u.val).points,
        Variety.mapPoints (schubertCellOfLE G u.val w u.property) p = q := by
  have hq : Variety.mapPoints (schubertInclusion G w) q ∈
      Set.range (Variety.mapPoints (schubertInclusion G w)) := ⟨q, rfl⟩
  rw [schubertVariety_points_cells] at hq
  obtain ⟨u, huw, hq⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨p, hp⟩ := hq
  refine ⟨⟨u, huw⟩, p, ?_⟩
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  rw [← Variety.mapPoints_comp, schubertCellOfLE_comp]
  exact hp
private theorem lower_cells_union (w : G.weylGroup) :
    (⋃ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      Set.range (schubertCellOfLE G u.val w u.property).left) = Set.univ := by
  let := weylGroup_finite G.rootBase
  have : JacobsonSpace (schubertVariety G w).toOver.left :=
    LocallyOfFiniteType.jacobsonSpace (schubertVariety G w).toSpec
  have hc (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w}) :
      IsConstructible (Set.range (schubertCellOfLE G u.val w u.property).left) :=
    Variety.isConstructible_range (schubertCellOfLE G u.val w u.property)
  apply constructible_eq (IsConstructible.iUnion hc) .univ
  ext p
  constructor
  · rintro ⟨_, hp⟩
    exact ⟨Set.mem_univ p, hp⟩
  · rintro ⟨_, hp⟩
    have hp' : p ∈ Set.range (schubertVariety G w).pointMap := by
      rw [Variety.pointMap_range]
      exact hp
    obtain ⟨q, rfl⟩ := hp'
    obtain ⟨u, z, hz⟩ := lower_points_cover G w q
    refine ⟨Set.mem_iUnion.mpr ⟨u, ⟨(schubertCell G u.val).pointMap z, ?_⟩⟩, hp⟩
    rw [← Variety.pointMap_mapPoints, hz]
private theorem lower_cells_unique (w : G.weylGroup)
    {u v : {u : G.weylGroup // WeylBruhatLE G.rootBase u w}}
    {q : (schubertVariety G w).scheme}
    (hu : q ∈ Set.range (schubertCellOfLE G u.val w u.property).left)
    (hv : q ∈ Set.range (schubertCellOfLE G v.val w v.property).left) : u = v := by
  apply Subtype.ext
  apply schubertCells_disjoint G (x := (schubertInclusion G w).left q)
  · obtain ⟨p, hp⟩ := hu
    refine ⟨p, ?_⟩
    exact (congrArg (fun f => f.left p) (schubertCellOfLE_comp G u.val w u.property)).symm.trans
      (congrArg (schubertInclusion G w).left hp)
  · obtain ⟨p, hp⟩ := hv
    refine ⟨p, ?_⟩
    exact (congrArg (fun f => f.left p) (schubertCellOfLE_comp G v.val w v.property)).symm.trans
      (congrArg (schubertInclusion G w).left hp)
/-- Every scheme point of a Schubert variety lies in exactly one lower cell. -/
theorem schubertLowerCells_partition (w : G.weylGroup) (q : (schubertVariety G w).scheme) :
    ∃! u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      q ∈ Set.range (schubertCellOfLE G u.val w u.property).left := by
  have hq : q ∈ ⋃ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      Set.range (schubertCellOfLE G u.val w u.property).left := by
    rw [lower_cells_union]
    exact Set.mem_univ q
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hq
  exact ⟨u, hu, fun v hv => lower_cells_unique G w hv hu⟩
omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_smul {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (q : X.points) :
    Variety.mapPoints f (t • q) = t • Variety.mapPoints f q := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • q) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f q)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom q)
private theorem lower_cell_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w})
    (b : (leviBorelVariety G I).points) (q : (schubertCell G u.val).points) :
    Variety.mapPoints (schubertCellOfLE G u.val w u.property) (b • q) =
      b • Variety.mapPoints (schubertCellOfLE G u.val w u.property) q :=
  equivariant_smul (H := leviBorelVariety G I)
    (schubertCellOfLE G u.val w u.property) b q
private def lowerCellOrbitMap (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w}) :
    MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G u.val).points →
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertVariety G w).points :=
  Quotient.map (Variety.mapPoints (schubertCellOfLE G u.val w u.property)) (by
    intro a b hab
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hab
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g, ?_⟩
    exact (lower_cell_smul G I w u g b).symm.trans
      (congrArg (Variety.mapPoints (schubertCellOfLE G u.val w u.property)) hg))
private def lowerOrbitMap (I : Set G.rootBase.support) (w : G.weylGroup) :
    (Σ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G u.val).points) →
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertVariety G w).points :=
  fun ⟨u, q⟩ => lowerCellOrbitMap G I w u q
private theorem lowerOrbit_mk_injective (I : Set G.rootBase.support) (w : G.weylGroup)
    (u v : {u : G.weylGroup // WeylBruhatLE G.rootBase u w})
    (a : (schubertCell G u.val).points) (b : (schubertCell G v.val).points)
    (he : (⟦Variety.mapPoints (schubertCellOfLE G u.val w u.property) a⟧ :
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points
          (schubertVariety G w).points) =
      ⟦Variety.mapPoints (schubertCellOfLE G v.val w v.property) b⟧) :
    (⟨u, ⟦a⟧⟩ : Σ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
      MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertCell G u.val).points) =
        ⟨v, ⟦b⟧⟩ := by
  have hrel : MulAction.orbitRel (leviBorelVariety G I).points
      (schubertVariety G w).points
      (Variety.mapPoints (schubertCellOfLE G u.val w u.property) a)
      (Variety.mapPoints (schubertCellOfLE G v.val w v.property) b) := Quotient.exact he
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
  have hgb : Variety.mapPoints (schubertCellOfLE G v.val w v.property) (g • b) =
      Variety.mapPoints (schubertCellOfLE G u.val w u.property) a :=
    (lower_cell_smul G I w v g b).trans hg
  have hu : (schubertVariety G w).pointMap
      (Variety.mapPoints (schubertCellOfLE G u.val w u.property) a) ∈
      Set.range (schubertCellOfLE G u.val w u.property).left :=
    ⟨(schubertCell G u.val).pointMap a,
      (Variety.pointMap_mapPoints (schubertCellOfLE G u.val w u.property) a).symm⟩
  have hv : (schubertVariety G w).pointMap
      (Variety.mapPoints (schubertCellOfLE G u.val w u.property) a) ∈
      Set.range (schubertCellOfLE G v.val w v.property).left :=
    ⟨(schubertCell G v.val).pointMap (g • b),
      (Variety.pointMap_mapPoints (schubertCellOfLE G v.val w v.property) (g • b)).symm.trans
        (congrArg (schubertVariety G w).pointMap hgb)⟩
  have huv : u = v := lower_cells_unique G w hu hv
  subst v
  apply congrArg (Sigma.mk u)
  apply Quotient.sound
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g, ?_⟩
  exact Variety.mapPoints_injective_of_mono (schubertCellOfLE G u.val w u.property) hgb
private theorem lowerOrbitMap_bijective (I : Set G.rootBase.support) (w : G.weylGroup) :
    Function.Bijective (lowerOrbitMap G I w) := by
  constructor
  · rintro ⟨u, a⟩ ⟨v, b⟩
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        exact lowerOrbit_mk_injective G I w u v a b
  · intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨u, p, hp⟩ := lower_points_cover G w q
      refine ⟨⟨u, ⟦p⟧⟩, ?_⟩
      change (⟦Variety.mapPoints (schubertCellOfLE G u.val w u.property) p⟧ :
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points
          (schubertVariety G w).points) = ⟦q⟧
      rw [hp]
/-- Levi--Borel orbits are the disjoint union of the lower-cell orbit quotients. -/
def schubertOrbitDecomposition (I : Set G.rootBase.support) (w : G.weylGroup) :
    MulAction.orbitRel.Quotient (leviBorelVariety G I).points (schubertVariety G w).points ≃
      Σ u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w},
        MulAction.orbitRel.Quotient (leviBorelVariety G I).points
          (schubertCell G u.val).points :=
  (Equiv.ofBijective (lowerOrbitMap G I w) (lowerOrbitMap_bijective G I w)).symm
/-- A lower-cell orbit maps to its ambient orbit through the cell inclusion. -/
theorem schubertOrbitDecomposition_symm_mk (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : {u : G.weylGroup // WeylBruhatLE G.rootBase u w})
    (q : (schubertCell G u.val).points) :
    (schubertOrbitDecomposition G I w).symm ⟨u, ⟦q⟧⟩ =
      ⟦Variety.mapPoints (schubertCellOfLE G u.val w u.property) q⟧ := rfl
end SchubertGeometry
