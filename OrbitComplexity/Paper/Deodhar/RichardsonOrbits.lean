import OrbitComplexity.Paper.Deodhar.ComponentWeights
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentCover
import OrbitComplexity.SchubertGeometry.Cells.RichardsonOrbitStrata
import OrbitComplexity.SchubertGeometry.Cells.RichardsonOpen
import OrbitComplexity.SchubertGeometry.Parabolics.Order
import OrbitComplexity.Paper.Deodhar.ComponentRichardson
import OrbitComplexity.BruhatIntervals.Graph.Labels

/-! # Maximum Richardson torus orbit dimension

The component cover and interval label spans bound every orbit. A general point
in the positive distinguished component attains the interval label rank.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open ReductiveGroups BruhatIntervals SchubertGeometry SchubertOrbits
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
attribute [local irreducible] deodharRichardsonMap richardsonCellToVariety

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_points {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) (x : X.points) :
    Variety.mapPoints f (h • x) = h • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (h • x) ≫ f = Y.pointsEquivOverHom (h • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom h) (X.pointsEquivOverHom x)

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_orbit {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (x : X.points) :
    Variety.mapPoints f '' MulAction.orbit H.points x =
      MulAction.orbit H.points (Variety.mapPoints f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hz
    rw [equivariant_points]
    exact MulAction.mem_orbit _ h
  · intro hy
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy
    exact ⟨h • x, MulAction.mem_orbit _ h, (equivariant_points f h x).trans hh⟩

private theorem cell_orbit_dimension (a b : G.weylGroup)
    (x : (richardsonCell G a b).points) :
    orbitNatDim (torusVariety G) (flagVariety G)
      (Variety.mapPoints (richardsonCellInclusion G a b) x) =
        orbitNatDim (torusVariety G) (richardsonCell G a b) x := by
  have h := orbit_image_dim (torusVariety G) (richardsonCell G a b)
    (flagVariety G) (richardsonCellInclusion G a b) x
  rw [equivariant_orbit (richardsonCellInclusion G a b) x] at h
  unfold orbitNatDim
  exact congrArg (fun d : WithBot ℕ∞ => (d.unbotD 0).toNat) h

private theorem flag_cell_bound_word
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (a : G.weylGroup)
    (x : (flagVariety G).points)
    (hx : (flagVariety G).pointMap x ∈
      Set.range (richardsonCellInclusion G a (simpleWeylWord G.rootBase word)).left) :
    orbitNatDim (torusVariety G) (flagVariety G) x ≤
      algebraicDim (weylRealization G.rootBase) a
        ((weylCoxeterSystem G.rootBase).wordProd word) := by
  rw [← deodharRichardson_cover G word hred a] at hx
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy⟩ := Variety.exists_mapPoints_eq (deodharInclusion G e.val hred) x he
  have hs := (subwordWeightSpan_interval (weylRealization G.rootBase)
    e.val hred e.property.1).1
  rw [e.property.2] at hs
  calc
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (mapPoints (deodharInclusion G e.val hred) y) :=
      congrArg (orbitNatDim (torusVariety G) (flagVariety G)) hy.symm
    _ = orbitNatDim (torusVariety G) (deodharComponent G e.val hred) y :=
      deodhar_orbitNatDim G e.val hred y
    _ ≤ subwordWeightDim (weylRealization G.rootBase) e.val :=
      deodharComponent_orbit_le G e.val hred e.property.1 y
    _ ≤ _ := Submodule.finrank_mono hs

private theorem flag_cell_bound (a b : G.weylGroup) (x : (flagVariety G).points)
    (hx : (flagVariety G).pointMap x ∈ Set.range (richardsonCellInclusion G a b).left) :
    orbitNatDim (torusVariety G) (flagVariety G) x ≤
      algebraicDim (weylRealization G.rootBase) a b := by
  obtain ⟨word, hred, hprod⟩ := (weylCoxeterSystem G.rootBase).exists_isReduced b
  have hb : simpleWeylWord G.rootBase word = b := by
    simpa only [weylCoxeterSystem_wordProd] using hprod.symm
  have hx' : (flagVariety G).pointMap x ∈
      Set.range (richardsonCellInclusion G a (simpleWeylWord G.rootBase word)).left := by
    exact Eq.mpr (congrArg (fun d : G.weylGroup =>
      (flagVariety G).pointMap x ∈ Set.range (richardsonCellInclusion G a d).left) hb) hx
  simpa only [weylCoxeterSystem_wordProd, hb] using flag_cell_bound_word G hred a x hx'

/-- The dimension of every Richardson torus orbit is bounded by the interval label rank. -/
theorem richardson_orbit_le (a b : G.weylGroup)
    (x : (richardsonVariety G a b).points) :
    orbitNatDim (torusVariety G) (richardsonVariety G a b) x ≤
      algebraicDim (weylRealization G.rootBase) a b := by
  obtain ⟨c, d, hac, _, hdb, y, _, hy⟩ := richardsonVariety_orbit_stratum G a b x
  have hmem : (flagVariety G).pointMap
      (mapPoints (richardsonCellInclusion G c d) y) ∈
      Set.range (richardsonCellInclusion G c d).left := by
    rw [Variety.pointMap_mapPoints]
    exact ⟨(richardsonCell G c d).pointMap y, rfl⟩
  calc
    _ = orbitNatDim (torusVariety G) (richardsonCell G c d) y := hy
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (mapPoints (richardsonCellInclusion G c d) y) :=
      (cell_orbit_dimension G c d y).symm
    _ ≤ algebraicDim (weylRealization G.rootBase) c d :=
      flag_cell_bound G c d _ hmem
    _ ≤ _ := Submodule.finrank_mono (labelSpan_mono (weylRealization G.rootBase)
      ((weyl_bruhat_iff G.rootBase a c).mp hac)
      ((weyl_bruhat_iff G.rootBase d b).mp hdb))

private theorem component_closed_point (e : Subexpression word)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) (a b : G.weylGroup)
    (hfinal : e.prefixProd (weylCoxeterSystem G.rootBase) word.length = a)
    (hupper : simpleWeylWord G.rootBase word = b)
    (y : (deodharComponent G e hred).points) :
    ∃ x : (richardsonVariety G a b).points,
      mapPoints (X := richardsonVariety G a b) (Y := flagVariety G)
        (richardsonInclusion G a b) x =
      mapPoints (X := deodharComponent G e hred) (Y := flagVariety G)
        (deodharInclusion G e hred) y := by
  let C := deodharComponent G e hred
  let R := richardsonCell G
    (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
    (simpleWeylWord G.rootBase word)
  let q : (flagVariety G).points :=
    mapPoints (X := C) (Y := flagVariety G) (deodharInclusion G e hred) y
  let t : R.points := mapPoints (X := C) (Y := R) (deodharRichardsonMap G e hred) y
  have ht : mapPoints (X := R) (Y := flagVariety G)
      (richardsonCellInclusion G
        (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)) t = q := by
    exact (Variety.mapPoints_comp (X := C) (Y := R) (Z := flagVariety G)
      (deodharRichardsonMap G e hred) (richardsonCellInclusion G
        (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)) y).symm.trans
      (congrArg (fun m : C.toOver ⟶ (flagVariety G).toOver =>
        mapPoints (X := C) (Y := flagVariety G) m y)
          (deodharRichardsonMap_comp G e hred))
  have hmem : (flagVariety G).pointMap q ∈ Set.range
      (richardsonCellInclusion G
        (e.prefixProd (weylCoxeterSystem G.rootBase) word.length)
        (simpleWeylWord G.rootBase word)).left := by
    rw [← ht, Variety.pointMap_mapPoints]
    exact ⟨R.pointMap t, rfl⟩
  have hmem' : (flagVariety G).pointMap q ∈
      Set.range (richardsonCellInclusion G a b).left :=
    Eq.mp (congrArg₂ (fun c d : G.weylGroup => (flagVariety G).pointMap q ∈
      Set.range (richardsonCellInclusion G c d).left) hfinal hupper) hmem
  obtain ⟨z, hz⟩ := Variety.exists_mapPoints_eq
    (X := richardsonCell G a b) (Y := flagVariety G)
    (richardsonCellInclusion G a b) q hmem'
  let x : (richardsonVariety G a b).points := mapPoints
    (X := richardsonCell G a b) (Y := richardsonVariety G a b)
    (richardsonCellToVariety G a b) z
  have hx : mapPoints (X := richardsonVariety G a b) (Y := flagVariety G)
      (richardsonInclusion G a b) x = q := by
    exact (Variety.mapPoints_comp (X := richardsonCell G a b)
      (Y := richardsonVariety G a b) (Z := flagVariety G)
      (richardsonCellToVariety G a b) (richardsonInclusion G a b) z).symm.trans
      ((congrArg (fun f : (richardsonCell G a b).toOver ⟶ (flagVariety G).toOver =>
        mapPoints (X := richardsonCell G a b) (Y := flagVariety G) f z)
          (richardsonCellToVariety_comp G a b)).trans hz)
  exact ⟨x, hx⟩

private theorem richardson_orbit_attains (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    ∃ x : (richardsonVariety G a b).points,
      orbitNatDim (torusVariety G) (richardsonVariety G a b) x =
        algebraicDim (weylRealization G.rootBase) a b := by
  obtain ⟨word, hred, hprod⟩ := (weylCoxeterSystem G.rootBase).exists_isReduced b
  have hb : simpleWeylWord G.rootBase word = b := by
    simpa only [weylCoxeterSystem_wordProd] using hprod.symm
  have hl : (weylCoxeterSystem G.rootBase).BruhatLE a
      ((weylCoxeterSystem G.rootBase).wordProd word) := by
    rwa [← hprod]
  obtain ⟨e, he, _⟩ := positive_subwordWeightSpan (weylRealization G.rootBase) hred a hl
  obtain ⟨y, hy⟩ := deodharComponent_orbit_attains G e hred he.2.1
  obtain ⟨x, hx⟩ := component_closed_point G e hred a b he.1 hb y
  refine ⟨x, ?_⟩
  calc
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (mapPoints (X := richardsonVariety G a b) (Y := flagVariety G)
          (richardsonInclusion G a b) x) :=
      (richardsonInclusion_orbitNatDim G a b x).symm
    _ = orbitNatDim (torusVariety G) (flagVariety G)
        (mapPoints (X := deodharComponent G e hred) (Y := flagVariety G)
          (deodharInclusion G e hred) y) :=
      congrArg (orbitNatDim (torusVariety G) (flagVariety G)) hx
    _ = orbitNatDim (torusVariety G) (deodharComponent G e hred) y :=
      deodhar_orbitNatDim G e hred y
    _ = subwordWeightDim (weylRealization G.rootBase) e := hy
    _ = _ := by simpa only [hprod] using he.2.2.2.2

/-- The interval label rank is the attained maximum Richardson torus orbit dimension. -/
theorem richardson_orbit_maximum (a b : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsGreatest {n : ℕ | ∃ x : (richardsonVariety G a b).points,
      orbitNatDim (torusVariety G) (richardsonVariety G a b) x = n}
      (algebraicDim (weylRealization G.rootBase) a b) := by
  refine ⟨richardson_orbit_attains G a b hle, ?_⟩
  rintro n ⟨x, rfl⟩
  exact richardson_orbit_le G a b x

end
end SchubertOrbits
