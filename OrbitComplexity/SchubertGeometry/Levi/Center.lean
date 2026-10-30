import OrbitComplexity.SchubertGeometry.Cells.RootPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviFactors
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviWeyl
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelNormalizer

/-!
# Centralizers and standard-parabolic generation

The unique unipotent Bruhat normal form of a centralizer point has its root
support in the selected Levi subsystem. The Weyl factor lies in the parabolic
Weyl subgroup, giving generation with the Borel by the selected reflections.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- In Bruhat normal form, a Levi point has a positive Levi-root unipotent factor. -/
theorem leviPoint_normalForm (I : Set G.rootBase.support)
    (g : G.points) (hg : g ∈ G.leviPoints I) :
    ∃ (w : G.weylGroup) (u : G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)) (b : G.borelPoints),
      (u : G.points) * G.weylPoint w * b = g ∧
        G.weylPoint w * b ∈ G.leviPoints I := by
  obtain ⟨w, u, hu⟩ := flagPoint_normalForm G (flagProjection G g)
  have hcomm : u.val ∈ G.leviPoints I := by
    intro z hz
    have ht := G.leviCenterPoints_le_torus I hz
    let v : schubertUnipotentPoints G w := ⟨z * u.val * z⁻¹,
      G.rootSubsetPoints_conjugate_mem _ _ z u.val ht u.property⟩
    have hleft : schubertPointMap G w v = z • schubertPointMap G w u := by
      change flagProjection G ((z * u.val * z⁻¹) * G.weylPoint w) =
        flagProjection G (z * (u.val * G.weylPoint w))
      apply (flagProjection_eq_iff G _ _).mpr
      have hT := (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) z).mp ht
      convert G.torus_le_borel hT using 1
      group
    have hfix : z • flagProjection G g = flagProjection G g := by
      change flagProjection G (z * g) = flagProjection G g
      rw [hg z hz]
      apply (flagProjection_eq_iff G _ _).mpr
      have hzB := G.borelPoints.inv_mem (G.torus_le_borel ht)
      convert hzB using 1
      group
    have hvu : v = u := (schubertPointMap_injective G w) (by rw [hleft, hu, hfix])
    exact (mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val hvu)
  have huI : u.val ∈ G.rootSubsetPoints (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
    rw [← G.levi_unipotent_eq I]
    exact ⟨hcomm, G.rootSubsetPoints_le_unipotent _ _ u.property⟩
  let b := (u.val * G.weylPoint w)⁻¹ * g
  have hb : b ∈ G.borelPoints := (flagProjection_eq_iff G _ _).mp hu
  refine ⟨w, ⟨u.val, huI⟩, ⟨b, hb⟩, ?_, ?_⟩
  · change u.val * G.weylPoint w * ((u.val * G.weylPoint w)⁻¹ * g) = g
    group
  · have h := (G.leviPoints I).mul_mem ((G.leviPoints I).inv_mem hcomm) hg
    convert h using 1
    dsimp [b]
    group

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_comm (s t : G.torusPoints) : s * t = t * s := by
  have hco : Coalgebra.IsCocomm K (CommHopfAlgCat.quotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal) :=
    G.torus_isTorus.isCocomm K G.torusAlgebra
  have hcomm : IsMulCommutative G.torusPoints :=
    @CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup K _
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.torusIdeal hco (CommAlgCat.of K K)
  exact @mul_comm' G.torusPoints _ hcomm s t

omit [IsAlgClosed K] [CharZero K] in
private theorem torus_conj_eq (s z : G.points)
    (hs : s ∈ G.torusPoints) (hz : z ∈ G.torusPoints) : s * z * s⁻¹ = z := by
  have h : s * z = z * s := congrArg Subtype.val
    (torus_comm G (⟨s, hs⟩ : G.torusPoints) ⟨z, hz⟩)
  exact (mul_inv_eq_iff_eq_mul).mpr h

private theorem borel_conj_torus_eq (b z : G.points) (hb : b ∈ G.borelPoints)
    (hz : z ∈ G.torusPoints) (hconj : b * z * b⁻¹ ∈ G.torusPoints) :
    b * z * b⁻¹ = z := by
  obtain ⟨t, ht, u, hu, htu⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive b hb
  have huvT : u * z * u⁻¹ ∈ G.torusPoints := by
    have hh := G.torusPoints.mul_mem
      (G.torusPoints.mul_mem (G.torusPoints.inv_mem ht) hconj) ht
    convert hh using 1
    rw [← htu]
    group
  have hcT : u * z * u⁻¹ * z⁻¹ ∈ G.torusPoints :=
    G.torusPoints.mul_mem huvT (G.torusPoints.inv_mem hz)
  have hzN := TorusPoints.le_normalizer_borelRootUnipotentPoints G.torusIdeal
    G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel G.torusSplit
    G.split_surjective G.split_eq_zero G.reductive hz
  have hzU : z * u⁻¹ * z⁻¹ ∈ G.unipotentPoints :=
    (Subgroup.mem_normalizer_iff.mp hzN u⁻¹).mp (G.unipotentPoints.inv_mem hu)
  have hcU : u * z * u⁻¹ * z⁻¹ ∈ G.unipotentPoints := by
    simpa only [mul_assoc] using G.unipotentPoints.mul_mem hu hzU
  have hc := BorelRootUnipotent.torus_point_intersection_eq_one G.torusIdeal
    G.borelIdeal G.isBorel G.torusSplit G.split_surjective G.split_eq_zero
    (u * z * u⁻¹ * z⁻¹) hcT hcU
  have huz : u * z * u⁻¹ = z := mul_inv_eq_one.mp hc
  calc
    b * z * b⁻¹ = t * (u * z * u⁻¹) * t⁻¹ := by rw [← htu]; group
    _ = z := by rw [huz]; exact torus_conj_eq G t z ht hz

/-- A Weyl--Borel product in the Levi has its Weyl representative in the Levi. -/
theorem levi_weyl_of_mul_borel (I : Set G.rootBase.support)
    (w : G.weylGroup) (b : G.points) (hb : b ∈ G.borelPoints)
    (hwb : G.weylPoint w * b ∈ G.leviPoints I) : G.weylPoint w ∈ G.leviPoints I := by
  intro z hz
  have ht := G.leviCenterPoints_le_torus I hz
  have hT : (G.weylPoint w)⁻¹ * z * G.weylPoint w ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer w) z).mp ht
  have hbz : b * z * b⁻¹ = (G.weylPoint w)⁻¹ * z * G.weylPoint w := by
    have hc := hwb z hz
    calc
      b * z * b⁻¹ = (G.weylPoint w)⁻¹ * ((G.weylPoint w * b) * z) * b⁻¹ := by group
      _ = (G.weylPoint w)⁻¹ * (z * (G.weylPoint w * b)) * b⁻¹ := by rw [hc]
      _ = (G.weylPoint w)⁻¹ * z * G.weylPoint w := by group
  have he := borel_conj_torus_eq G b z hb ht (hbz.symm ▸ hT)
  have hn : (G.weylPoint w)⁻¹ * z * G.weylPoint w = z := hbz.symm.trans he
  have h := congrArg (fun x : G.points => G.weylPoint w * x) hn
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h

/-- The Levi and Borel generate the subgroup generated by the Borel and selected reflections. -/
theorem levi_sup_borel_eq (I : Set G.rootBase.support) :
    G.leviPoints I ⊔ G.borelPoints = G.borelPoints ⊔
      Subgroup.closure ((fun i : G.rootBase.support => G.reflectionPoint i.val) '' I) := by
  let H := G.borelPoints ⊔
    Subgroup.closure ((fun i : G.rootBase.support => G.reflectionPoint i.val) '' I)
  have hBH : G.borelPoints ≤ H := le_sup_left
  have hTH : G.torusPoints ≤ H := G.torus_le_borel.trans hBH
  apply le_antisymm
  · apply sup_le _ hBH
    intro g hg
    obtain ⟨w, u, b, hprod, hwb⟩ := leviPoint_normalForm G I g hg
    have hnL := levi_weyl_of_mul_borel G I w b b.property hwb
    have hw := (G.weylPoint_mem_levi_iff I w).mp hnL
    obtain ⟨l, hl, hword⟩ := (mem_standardParabolicSubgroup_iff_word G.rootBase I w).mp hw
    have hp : simpleWordPoint G.reflectionPoint G.rootBase l ∈ H := by
      change (l.map (fun i : G.rootBase.support => G.reflectionPoint i.val)).prod ∈ H
      apply Subgroup.list_prod_mem
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      exact (show Subgroup.closure
        ((fun i : G.rootBase.support => G.reflectionPoint i.val) '' I) ≤ H from le_sup_right)
          (Subgroup.subset_closure ⟨i, hl i hi, rfl⟩)
    obtain ⟨t, ht, he⟩ := G.isBruhatSystem.weyl.simpleWordPoint_eq_mul_weylElementPoint
      G.rootBase l
    rw [hword, ← G.weylPoint_eq] at he
    have hn : G.weylPoint w ∈ H := by
      have hh := H.mul_mem (H.inv_mem (hTH ht)) hp
      rwa [he, inv_mul_cancel_left] at hh
    have huH : (u : G.points) ∈ H := hBH
      (G.unipotent_le_borel (G.rootSubsetPoints_le_unipotent _ _ u.property))
    exact hprod ▸ H.mul_mem (H.mul_mem huH hn) (hBH b.property)
  · apply sup_le le_sup_right
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (le_sup_left : G.leviPoints I ≤ G.leviPoints I ⊔ G.borelPoints)
      (G.reflectionPoint_mem_levi I i hi)

end SchubertGeometry
