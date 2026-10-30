import OrbitComplexity.GroupActions.Representations.ExteriorDegrees
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight

/-! # Rational actions on exterior powers

Evaluating the exterior coaction at a group point gives the exterior power of the
original point action. The inclusion into the exterior algebra intertwines these actions.
-/

noncomputable section
namespace GroupActions
open TauCeti WithConv
open scoped TensorProduct
universe u v w
variable {K : Type u} {H : Type v} {V : Type w}
  [Field K] [CharZero K] [CommRing H] [HopfAlgebra K H]
  [AddCommGroup V] [Module K V] [Comodule K H V]

private def pointEvaluation (g : WithConv (H →ₐ[K] K)) :
    (ExteriorAlgebra K V) ⊗[K] H →ₐ[K] ExteriorAlgebra K V :=
  (Algebra.TensorProduct.rid K K (ExteriorAlgebra K V)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K (ExteriorAlgebra K V)) g.ofConv)

omit [CharZero K] in
private theorem base_action (g : WithConv (H →ₐ[K] K)) (v : V) :
    Comodule.basePointsRepresentation (R := K) (H := H) V g v =
      TensorProduct.rid K V
        (LinearMap.lTensor V g.ofConv.toLinearMap (Comodule.coact (R := K) (C := H) v)) := by
  rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, one_smul,
    TensorProduct.lid_comm]

omit [CharZero K] [Comodule K H V] in
private theorem evaluation_ι (g : WithConv (H →ₐ[K] K)) (z : V ⊗[K] H) :
    pointEvaluation g (TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id z) =
      ExteriorAlgebra.ι K
        (TensorProduct.rid K V (LinearMap.lTensor V g.ofConv.toLinearMap z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul v h => simp [pointEvaluation]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem exteriorPoint_eq (g : WithConv (H →ₐ[K] K)) :
    (pointEvaluation g).comp (GroupActions.exteriorCoact (V := V)) =
      ExteriorAlgebra.map (Comodule.basePointsRepresentation (R := K) (H := H) V g) := by
  ext v
  change pointEvaluation g (GroupActions.exteriorCoact (ExteriorAlgebra.ι K v)) =
    ExteriorAlgebra.map (Comodule.basePointsRepresentation (R := K) (H := H) V g)
      (ExteriorAlgebra.ι K v)
  rw [GroupActions.exteriorCoact_ι, evaluation_ι, ExteriorAlgebra.map_apply_ι, base_action]

private theorem degree_point_coe (d : ℕ) (g : WithConv (H →ₐ[K] K)) (x : ⋀[K]^d V) :
    letI := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := V) d
    ((Comodule.basePointsRepresentation (R := K) (H := H) (⋀[K]^d V) g x :
      ⋀[K]^d V) : ExteriorAlgebra K V) =
        pointEvaluation g (GroupActions.exteriorCoact x.val) := by
  let := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := V) d
  have ht (z : (⋀[K]^d V) ⊗[K] H) :
      ((TensorProduct.rid K (⋀[K]^d V) (LinearMap.lTensor _ g.ofConv.toLinearMap z) :
        ⋀[K]^d V) : ExteriorAlgebra K V) =
      TensorProduct.rid K (ExteriorAlgebra K V)
        (LinearMap.lTensor _ g.ofConv.toLinearMap
          (TensorProduct.map (⋀[K]^d V).subtype LinearMap.id z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul x h => simp
    | add z w hz hw => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hz hw
  rw [base_action, ht, GroupActions.exteriorPower_coact]
  rfl


/-- The rational-point action on an exterior power is the exterior power of the point action. -/
theorem exteriorPower_basePoints (d : ℕ) (g : WithConv (H →ₐ[K] K)) :
    letI := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := V) d
    Comodule.basePointsRepresentation (R := K) (H := H) (⋀[K]^d V) g =
      Representation.exteriorPower
        (Comodule.basePointsRepresentation (R := K) (H := H) V) d g := by
  let := GroupActions.exteriorPowerComodule (K := K) (H := H) (V := V) d
  apply LinearMap.ext
  intro x
  apply Subtype.val_injective
  change ((Comodule.basePointsRepresentation (R := K) (H := H) (⋀[K]^d V) g x :
    ⋀[K]^d V) : ExteriorAlgebra K V) =
      (exteriorPower.map d (Comodule.basePointsRepresentation (R := K) (H := H) V g) x).val
  rw [degree_point_coe]
  rw [exteriorPower.coe_map]
  exact AlgHom.congr_fun (exteriorPoint_eq g) x.val

end GroupActions

noncomputable section
namespace GroupActions
open TauCeti
open scoped TensorProduct BigOperators
universe u v w x
variable {K : Type u} {H : Type v} {V : Type w} {M : Type x}
  [Field K] [CharZero K] [CommRing H] [HopfAlgebra K H]
  [AddCommGroup V] [Module K V] [Comodule K H V] [CommGroup M]

/-- Wedges of a character basis are character vectors of the exterior comodule. -/
theorem exteriorBasis_weightSpace {r : ℕ} (π : H →ₐc[K] MonoidAlgebra K M)
    (b : Module.Basis (Fin r) K V) (χ : Fin r → M)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V π.toCoalgHom (χ i))
    (d : ℕ) (s : Set.powersetCard (Fin r) d) :
    letI := exteriorPowerComodule (K := K) (H := H) (V := V) d
    b.exteriorPower d s ∈ DiagonalizableGroup.weightSpace (⋀[K]^d V) π.toCoalgHom
      (∏ i ∈ s.val, χ i) := by
  classical
  let := exteriorPowerComodule (K := K) (H := H) (V := V) d
  apply DiagonalizableGroup.mem_weightSpace.mpr
  let c : ExteriorAlgebra K V →ₐ[K]
      ExteriorAlgebra K V ⊗[K] MonoidAlgebra K M :=
    (Algebra.TensorProduct.map (AlgHom.id K (ExteriorAlgebra K V))
      π.toAlgHom).comp
      (GroupActions.exteriorCoact (K := K) (H := H))
  have hgen (i : Fin r) :
      c (ExteriorAlgebra.ι K (b i)) =
        ExteriorAlgebra.ι K (b i) ⊗ₜ[K]
          MonoidAlgebra.single (χ i) (1 : K) := by
    change TensorProduct.map LinearMap.id π.toCoalgHom.toLinearMap
      (GroupActions.exteriorCoact (K := K) (H := H)
        (ExteriorAlgebra.ι K (b i))) = _
    rw [GroupActions.exteriorCoact_ι]
    have hi := congrArg
      (TensorProduct.map (ExteriorAlgebra.ι K) LinearMap.id)
      (DiagonalizableGroup.mem_weightSpace.mp (hb i))
    simpa only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
      TensorProduct.map_tmul, LinearMap.id_apply] using hi
  have hprod (l : List (Fin r)) :
      c ((l.map fun i => ExteriorAlgebra.ι K (b i)).prod) =
        (l.map fun i => ExteriorAlgebra.ι K (b i)).prod ⊗ₜ[K]
          MonoidAlgebra.single (l.map (χ)).prod (1 : K) := by
    induction l with
    | nil => simp [Algebra.TensorProduct.one_def, MonoidAlgebra.one_def]
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, hgen, ih,
          Algebra.TensorProduct.tmul_mul_tmul, MonoidAlgebra.single_mul_single, one_mul]
  let j := Set.powersetCard.ofFinEmbEquiv.symm s
  have hp : (List.ofFn fun k : Fin d => χ (j k)).prod =
      (∏ i ∈ s.val, χ i) := by
    rw [List.prod_ofFn]
    change (∏ k : Fin d, χ (j k)) =
      ∏ i ∈ s.val, χ i
    apply Finset.prod_bij (fun k _ => j k)
    · intro k hk
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (j k)).mp
        ⟨k, rfl⟩
    · intro k hk l hl hkl
      exact j.injective hkl
    · intro i hi
      obtain ⟨k, hk⟩ :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
      exact ⟨k, Finset.mem_univ _, hk⟩
    · intro k hk
      rfl
  have he : c ((b.exteriorPower d) s).val =
      ((b.exteriorPower d) s).val ⊗ₜ[K]
        MonoidAlgebra.single ((∏ i ∈ s.val, χ i)) (1 : K) := by
    have hl := hprod (List.ofFn j)
    simp only [List.map_ofFn, Function.comp_def] at hl
    rw [hp] at hl
    simpa only [exteriorPower.basis_apply,
      exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family,
      ExteriorAlgebra.ιMulti_apply, Function.comp_def, j] using hl
  let := exteriorPowerComodule (K := K) (H := H) (V := V) d
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (M := MonoidAlgebra K M) (⋀[K]^d V).subtype
    (⋀[K]^d V).injective_subtype
  calc
    _ = TensorProduct.map LinearMap.id π.toCoalgHom.toLinearMap
        (TensorProduct.map (⋀[K]^d V).subtype LinearMap.id
          ((GroupActions.exteriorPowerComodule (K := K) (H := H)
            (V := V) d).coact ((b.exteriorPower d) s))) := by
      simp only [LinearMap.rTensor_def, TensorProduct.map_map, LinearMap.comp_id,
        LinearMap.id_comp]
    _ = c ((b.exteriorPower d) s).val := by
      rw [GroupActions.exteriorPower_coact]
      rfl
    _ = _ := he


end GroupActions
