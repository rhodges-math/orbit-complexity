import OrbitComplexity.GroupActions.Rosenlicht.InvariantRelations
import OrbitComplexity.GroupActions.Rosenlicht.FixedFields
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Descent of invariant polynomial relations

Over a field of invariant coefficients, a polynomial relation at a tuple is
equivalent to a relation at every group translate. If invariant-coefficient
polynomials generate the orbit ideal, extension of the contracted relation ideal
recovers the full orbit ideal.

## Main results

* `orbitIdeal_comap_eq`: invariant-coefficient relations descend by contraction.
* `orbitIdeal_map_comap_eq`: generators over a coefficient field give extension equality.
* `tensor_eq_iff_mem`: tensor equality detects membership in a coefficient field.
* `fixedField_fg`: invariant fields of finitely generated field actions are finitely generated.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w z

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {ι : Type z}

/-- The two tensor copies of an element agree exactly when it belongs to the base field. -/
theorem tensor_eq_iff_mem (E : IntermediateField K F) (f : F) :
    f ⊗ₜ[E] (1 : F) = (1 : F) ⊗ₜ[E] f ↔ f ∈ E := by
  have h := Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (Algebra.IsEffective.of_faithfullyFlat E F)
  have hh := Set.ext_iff.mp h f
  change (f ⊗ₜ[E] (1 : F) = (1 : F) ⊗ₜ[E] f) ↔
    f ∈ Set.range (algebraMap E F) at hh
  rw [hh]
  constructor
  · rintro ⟨e, rfl⟩
    exact e.property
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

private def tensorRelationMap (E : IntermediateField K F) (x : ι → F) :
    MvPolynomial ι F →+* F ⊗[E] F :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
    (fun i ↦ Algebra.TensorProduct.includeRight (x i))

private lemma tensorRelationMap_map (E : IntermediateField K F) (x : ι → F)
    (p : MvPolynomial ι E) :
    tensorRelationMap E x (MvPolynomial.map E.subtype p) =
      Algebra.TensorProduct.includeRight (MvPolynomial.aeval x p) := by
  change MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
    (fun i ↦ Algebra.TensorProduct.includeRight (x i)) (MvPolynomial.map E.subtype p) =
      (Algebra.TensorProduct.includeRight : F →ₐ[E] F ⊗[E] F).toRingHom
        (MvPolynomial.eval₂Hom E.subtype x p)
  rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
  congr 2
  ext c
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul c

private lemma tensorRelationMap_base (E : IntermediateField K F) (x : ι → F)
    (p : MvPolynomial ι K) :
    tensorRelationMap E x (MvPolynomial.map (algebraMap K F) p) =
      Algebra.TensorProduct.includeRight (MvPolynomial.aeval x p) := by
  change MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
    (fun i ↦ Algebra.TensorProduct.includeRight (x i))
      (MvPolynomial.map (algebraMap K F) p) =
      (Algebra.TensorProduct.includeRight : F →ₐ[E] F ⊗[E] F).toRingHom
        (MvPolynomial.eval₂Hom (algebraMap K F) x p)
  rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
  congr 2
  ext c
  change algebraMap K F c ⊗ₜ[E] (1 : F) = (1 : F) ⊗ₜ[E] algebraMap K F c
  simpa only [IsScalarTower.algebraMap_apply K E F] using
    (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap K E c) :
      algebraMap E F (algebraMap K E c) ⊗ₜ[E] 1 =
        (1 : F) ⊗ₜ[E] algebraMap E F (algebraMap K E c))

variable {G : Type w} [Group G] [MulSemiringAction G F] [SMulCommClass G K F]

/-- Over invariant coefficients, the ordinary relation ideal of a tuple is the
contraction of its orbit relation ideal. -/
theorem orbitIdeal_comap_eq (E : IntermediateField K F)
    (hE : E ≤ (FixedPoints.intermediateField (F := K) G : IntermediateField K F))
    (x : ι → F) :
    Ideal.comap (MvPolynomial.map E.subtype) (orbitIdeal (G := G) x) =
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι E →ₐ[E] F) := by
  ext p
  change MvPolynomial.map E.subtype p ∈ orbitIdeal (G := G) x ↔
    MvPolynomial.aeval x p = 0
  rw [mem_orbitIdeal_iff]
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  change (∀ g : G, MvPolynomial.eval₂Hom E.subtype
    (fun i ↦ g • x i) p = 0) ↔
      MvPolynomial.eval₂Hom E.subtype x p = 0
  constructor
  · intro hp
    simpa only [one_smul] using hp 1
  · intro hp g
    have hc : (MulSemiringAction.toRingHom G F g).comp E.subtype =
        E.subtype := by
      ext c
      exact hE c.property g
    have hg := MvPolynomial.map_eval₂Hom E.subtype x
      (MulSemiringAction.toRingHom G F g) p
    rw [hc] at hg
    exact hg.symm.trans (by rw [hp, map_zero])

omit [SMulCommClass G K F] in
/-- Orbit ideal generators with coefficients in a subfield make the orbit ideal
the scalar extension of its contraction to that coefficient field. -/
theorem orbitIdeal_map_comap_eq (E : IntermediateField K F) (x : ι → F)
    (s : Set (MvPolynomial ι F)) (hs : Ideal.span s = orbitIdeal (G := G) x)
    (hc : ∀ p ∈ s, ∀ m, p.coeff m ∈ E) :
    (Ideal.comap (MvPolynomial.map E.subtype) (orbitIdeal (G := G) x)).map
      (MvPolynomial.map E.subtype) = orbitIdeal (G := G) x := by
  apply le_antisymm Ideal.map_comap_le
  conv_lhs => rw [← hs]
  apply Ideal.span_le.mpr
  intro p hp
  have hp' : p ∈ Set.range (MvPolynomial.map E.subtype) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc'
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
    exact ⟨⟨p.coeff m, hc p hp m⟩, rfl⟩
  obtain ⟨q, hq⟩ := hp'
  have hq' : q ∈ Ideal.comap (MvPolynomial.map E.subtype)
      (orbitIdeal (G := G) x) := by
    change MvPolynomial.map E.subtype q ∈ orbitIdeal (G := G) x
    rw [hq, ← hs]
    exact Ideal.subset_span hp
  rw [← hq]
  exact Ideal.mem_map_of_mem _ hq'

private lemma orbitIdeal_le_tensorKer (E : IntermediateField K F)
    (hE : E ≤ (FixedPoints.intermediateField (F := K) G : IntermediateField K F))
    (x : ι → F) (s : Set (MvPolynomial ι F))
    (hs : Ideal.span s = orbitIdeal (G := G) x) (hc : ∀ p ∈ s, ∀ m, p.coeff m ∈ E) :
    orbitIdeal (G := G) x ≤ RingHom.ker (tensorRelationMap E x) := by
  rw [← orbitIdeal_map_comap_eq E x s hs hc]
  apply Ideal.map_le_iff_le_comap.mpr
  rw [orbitIdeal_comap_eq E hE x]
  intro p hp
  change tensorRelationMap E x (MvPolynomial.map E.subtype p) = 0
  rw [tensorRelationMap_map]
  have hp' : MvPolynomial.aeval x p = 0 := hp
  simpa only [map_zero] using congrArg
    (Algebra.TensorProduct.includeRight : F →ₐ[E] F ⊗[E] F) hp'

private lemma fixed_mem_coefficientField (E : IntermediateField K F)
    (hE : E ≤ (FixedPoints.intermediateField (F := K) G : IntermediateField K F))
    (x : ι → F) (hx : IntermediateField.adjoin K (Set.range x) = ⊤)
    (s : Set (MvPolynomial ι F)) (hs : Ideal.span s = orbitIdeal (G := G) x)
    (hc : ∀ p ∈ s, ∀ m, p.coeff m ∈ E) {f : F}
    (hf : f ∈ (FixedPoints.intermediateField (F := K) G : IntermediateField K F)) : f ∈ E := by
  by_cases hf0 : f = 0
  · simpa only [hf0] using E.zero_mem
  have hxf : f ∈ IntermediateField.adjoin K (Set.range x) := by rw [hx]; trivial
  obtain ⟨P, Q, hfPQ⟩ := (IntermediateField.mem_adjoin_range_iff K x f).mp hxf
  have hQ : MvPolynomial.aeval x Q ≠ 0 := by
    intro hQ
    rw [hQ, div_zero] at hfPQ
    exact hf0 hfPQ
  let r := MvPolynomial.map (algebraMap K F) P -
    MvPolynomial.C f * MvPolynomial.map (algebraMap K F) Q
  have hident : MvPolynomial.eval x r = 0 := by
    dsimp only [r]
    simp only [map_sub, map_mul, MvPolynomial.eval_C]
    change MvPolynomial.eval₂Hom (RingHom.id F) x
        (MvPolynomial.map (algebraMap K F) P) -
      f * MvPolynomial.eval₂Hom (RingHom.id F) x
        (MvPolynomial.map (algebraMap K F) Q) = 0
    rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.eval₂Hom_map_hom]
    change MvPolynomial.aeval x P - f * MvPolynomial.aeval x Q = 0
    exact sub_eq_zero.mpr ((eq_div_iff hQ).mp hfPQ).symm
  have hr : r ∈ orbitIdeal (G := G) x := by
    rw [mem_orbitIdeal_iff]
    intro g
    have hK : (MulSemiringAction.toRingHom G F g).comp (algebraMap K F) =
        algebraMap K F := by
      ext c
      exact (MulSemiringAction.toAlgHom K F g).commutes c
    have hfg : g • f = f := hf g
    have hrfix : MvPolynomial.map (MulSemiringAction.toRingHom G F g) r = r := by
      simp only [r, map_sub, map_mul, MvPolynomial.map_map, MvPolynomial.map_C,
        hK, MulSemiringAction.toRingHom_apply, hfg]
    have he := congrArg (MulSemiringAction.toRingHom G F g) hident
    rw [map_zero, MvPolynomial.map_eval, hrfix] at he
    exact he
  have hrel : tensorRelationMap E x r = 0 := orbitIdeal_le_tensorKer E hE x s hs hc hr
  have hC : tensorRelationMap E x (MvPolynomial.C f) =
      (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F) f := by
    simp [tensorRelationMap]
  simp only [r, map_sub, map_mul, hC, tensorRelationMap_base] at hrel
  let lF := (Algebra.TensorProduct.includeLeft : F →ₐ[E] F ⊗[E] F).toRingHom
  let rF := (Algebra.TensorProduct.includeRight : F →ₐ[E] F ⊗[E] F).toRingHom
  have hPQ : rF (MvPolynomial.aeval x P) = rF f * rF (MvPolynomial.aeval x Q) := by
    simpa only [map_mul] using congrArg rF ((eq_div_iff hQ).mp hfPQ).symm
  have hQu : IsUnit (rF (MvPolynomial.aeval x Q)) :=
    (isUnit_iff_ne_zero.mpr hQ).map rF
  have heq : lF f = rF f :=
    hQu.mul_left_inj.mp ((sub_eq_zero.mp hrel).symm.trans hPQ)
  exact (tensor_eq_iff_mem E f).mp heq

variable [Algebra.EssFiniteType K F]

/-- The invariant subfield of a finitely generated field extension is finitely generated. -/
theorem fixedField_fg :
    (FixedPoints.intermediateField (F := K) G : IntermediateField K F).FG := by
  classical
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K F
  let x : t → F := Subtype.val
  have hxr : Set.range x = (t : Set F) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  have hx : IntermediateField.adjoin K (Set.range x) = ⊤ := by rw [hxr]; exact ht
  obtain ⟨s, hs, hcoeff⟩ := exists_fixed_orbitIdeal_generators (G := G) x
  let c := s.biUnion fun p ↦ p.coeffs
  let E := IntermediateField.adjoin K (c : Set F)
  have hE : E ≤ (FixedPoints.intermediateField (F := K) G : IntermediateField K F) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro f hf
    obtain ⟨p, hp, hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hf
    exact fun g ↦ hcoeff p hp g m
  have hc : ∀ p ∈ (s : Set (MvPolynomial t F)), ∀ m, p.coeff m ∈ E := by
    intro p hp m
    by_cases hm : p.coeff m = 0
    · rw [hm]
      exact E.zero_mem
    apply IntermediateField.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨p, hp, MvPolynomial.coeff_mem_coeffs m hm⟩
  have hEF : E = (FixedPoints.intermediateField (F := K) G : IntermediateField K F) :=
    le_antisymm hE fun f hf ↦ fixed_mem_coefficientField E hE x hx _ hs hc hf
  exact ⟨c, hEF⟩

/-- An invariant subfield of a finitely generated field extension is essentially
of finite type over the base field. -/
theorem fixedField_essFiniteType :
    Algebra.EssFiniteType K
      (FixedPoints.intermediateField (F := K) G : IntermediateField K F) :=
  IntermediateField.essFiniteType_iff.mpr (fixedField_fg (G := G))

end

end GroupActions
