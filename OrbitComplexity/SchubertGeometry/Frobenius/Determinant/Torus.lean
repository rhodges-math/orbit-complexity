import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Section
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBruhatDisjoint
import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-! # The determinant coefficient and the torus action -/

open ReductiveGroups TauCeti GroupActions
open scoped TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The algebraic exterior comodule evaluates to the exterior adjoint action. -/
theorem adjointExterior_points (g : G.points)
    (x : ⋀[K]^(Module.finrank K G.unipotentTangent) G.tangent) :
    letI := adjointExteriorComodule G
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _ g x =
      exteriorPower.map (Module.finrank K G.unipotentTangent)
        (affineGroupAdjointRepresentation g) x := by
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra)
    (V := G.tangent) (Module.finrank K G.unipotentTangent)
  rw [exteriorPower_basePoints, Representation.exteriorPower_apply,
    affineGroupAdjointComodule_points]

omit [IsAlgClosed K] [CharZero K] in
private theorem wedge_map {V : Type u} [AddCommGroup V] [Module K V]
    (F : Submodule K V) [Module.Finite K F]
    (a : Module.End K F) (b : Module.End K V)
    (hc : F.subtype.comp a = b.comp F.subtype) :
    exteriorPower.map (Module.finrank K F) b
        (exteriorPower.map (Module.finrank K F) F.subtype
          (exteriorPower.ιMulti K _ (Module.finBasis K F))) =
      LinearMap.det a • exteriorPower.map (Module.finrank K F) F.subtype
        (exteriorPower.ιMulti K _ (Module.finBasis K F)) := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, ← hc,
    exteriorPower.map_comp, LinearMap.comp_apply, exteriorPower.map_finrank_eq_det_smul,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- The exterior point action scales the positive determinant vector by full delta. -/
theorem positiveDet_torus
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    letI := adjointExteriorComodule G
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _
      (TauCeti.AlgHom.mapDomain G.torusSplit z) (positiveDetVector G) =
        z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) • positiveDetVector G := by
  rw [adjointExterior_points]
  have hv := wedge_map G.unipotentTangent.toSubmodule (positiveTorusEnd G z)
    (affineGroupAdjointRepresentation (TauCeti.AlgHom.mapDomain G.torusSplit z))
    (positiveTorusEnd_subtype G z)
  rw [positiveTorus_determinant] at hv
  exact hv

/-- The regular coefficient has the full right-torus character on all group points. -/
theorem positiveDet_right_torus (g : G.points)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    (g * TauCeti.AlgHom.mapDomain G.torusSplit z).ofConv (positiveDetCoefficient G) =
      z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) *
        g.ofConv (positiveDetCoefficient G) := by
  let := adjointExteriorComodule G
  change (g * TauCeti.AlgHom.mapDomain G.torusSplit z).ofConv
      (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (positiveDetVector G)) =
    z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) * g.ofConv
      (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (positiveDetVector G))
  rw [Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient,
    map_mul, Module.End.mul_apply, positiveDet_torus]
  simp only [map_smul, smul_eq_mul]

end SchubertGeometry.DeterminantSection



namespace SchubertGeometry.DeterminantSection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem det_of_disjoint_sum (F P Q : Submodule K V)
    [Module.Finite K P] [Module.Finite K Q]
    (hF : F = P ⊔ Q) (hd : Disjoint P Q)
    (e : V ≃ₗ[K] V) (he : F.map e.toLinearMap = F)
    (f : Module.End K Q) (hP : ∀ x : P, e x = (x : V))
    (hQ : Q.subtype.comp f = e.toLinearMap.comp Q.subtype) :
    LinearMap.det (e.ofSubmodules F F he).toLinearMap = LinearMap.det f := by
  let s : (P × Q) →ₗ[K] F := (P.subtype.coprod Q.subtype).codRestrict F (by
    intro x
    rw [hF]
    exact Submodule.add_mem_sup x.1.property x.2.property)
  have hs₀ : Function.Injective (P.subtype.coprod Q.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range,
      Submodule.ker_subtype, Submodule.ker_subtype, Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using hd
  have hs : Function.Bijective s := by
    constructor
    · intro x y h
      exact hs₀ (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩
      rw [hF] at hv
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective s hs
  have hc : (e.ofSubmodules F F he).toLinearMap.comp E.toLinearMap =
      E.toLinearMap.comp (LinearMap.prodMap (LinearMap.id : Module.End K P) f) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e ((x.1 : V) + (x.2 : V)) = (x.1 : V) + (f x.2 : V)
    rw [map_add, hP]
    exact congrArg ((x.1 : V) + ·) (LinearMap.congr_fun hQ x.2).symm
  have hconj : (e.ofSubmodules F F he).toLinearMap =
      E.toLinearMap.comp
        ((LinearMap.prodMap (LinearMap.id : Module.End K P) f).comp E.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    change (e.ofSubmodules F F he) x =
      E (LinearMap.prodMap (LinearMap.id : Module.End K P) f (E.symm x))
    have h := LinearMap.congr_fun hc (E.symm x)
    change (e.ofSubmodules F F he) (E (E.symm x)) =
      E (LinearMap.prodMap (LinearMap.id : Module.End K P) f (E.symm x)) at h
    rw [E.apply_symm_apply] at h
    exact h
  rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

end SchubertGeometry.DeterminantSection

namespace SchubertGeometry.DeterminantSection
open ReductiveGroups TauCeti
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The determinant on the Borel tangent is the full positive-root character. -/
theorem borelTorus_determinant
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (hB : G.borelTangent.toSubmodule.map
      (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z)) =
        G.borelTangent.toSubmodule) :
    LinearMap.det (LinearEquiv.ofSubmodules
      (affineGroupAdjointLieEquiv (AlgHom.mapDomain G.torusSplit z)).toLinearEquiv
      G.borelTangent.toSubmodule G.borelTangent.toSubmodule hB).toLinearMap =
      z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) := by
  have h := det_of_disjoint_sum G.borelTangent.toSubmodule G.torusTangent.toSubmodule
    G.unipotentTangent.toSubmodule (G.borelTangent_eq_sup) (G.torus_disjoint_unipotent)
    (affineGroupAdjointLieEquiv (AlgHom.mapDomain G.torusSplit z)).toLinearEquiv hB
    (positiveTorusEnd G z) (torusTangent_fixed G z) (positiveTorusEnd_subtype G z)
  exact h.trans (positiveTorus_determinant G z)

/-- The top Borel exterior vector has the full positive-root torus character. -/
theorem borelTop_torus
    (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
    (hdet : ∀ (e : G.tangent ≃ₗ[K] G.tangent)
      (hB : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
      exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule) e.toLinearMap w =
        LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
          G.borelTangent.toSubmodule hB).toLinearMap • w)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
      (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z)) w =
        z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) • w := by
  have ht := mapDomain_mem_torusPoints G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero z
  have hB := G.borelTangent_map_adjoint (AlgHom.mapDomain G.torusSplit z)
    (G.torus_le_borel ht)
  have h := hdet (affineGroupAdjointLieEquiv (AlgHom.mapDomain G.torusSplit z)).toLinearEquiv hB
  rw [borelTorus_determinant G z hB] at h
  exact h

end SchubertGeometry.DeterminantSection
