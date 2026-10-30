import OrbitComplexity.FrobeniusSplitting.Cartier.AffineSections
import OrbitComplexity.FrobeniusSplitting.Cartier.DualWeights
import OrbitComplexity.FrobeniusSplitting.Cartier.TraceFrame

/-! # Local operators in residue coordinates -/

open AlgebraicGeometry CategoryTheory Opposite Polynomial
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

variable (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

private abbrev affineLine := Spec (.of (Polynomial C))
private abbrev residueIndex := ULift.{u} (Fin p)

private def affineBase : affineLine C ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : C →+* Polynomial C))

private def alpha := sheafFrobenius C p (affineBase C)

private def coordinateMap (U : (affineLine C).Opens) :
    Polynomial C →+* Γ(affineLine C, U) :=
  ((Scheme.ΓSpecIso (.of (Polynomial C))).inv ≫
    (affineLine C).presheaf.map U.leTop.op).hom

private theorem coordinateMap_res (U : (affineLine C).Opens) (V : Over U)
    (f : Polynomial C) :
    (affineLine C).presheaf.map V.hom.op (coordinateMap C U f) =
      coordinateMap C V.left f := by
  have h := congrArg
    (fun k : Γ(affineLine C, ⊤) ⟶ Γ(affineLine C, V.left) =>
      k ((Scheme.ΓSpecIso (.of (Polynomial C))).inv f))
    ((affineLine C).presheaf.map_comp U.leTop.op V.hom.op)
  exact h.symm

private theorem section_expansion (U : (affineLine C).Opens)
    (m : Γ(affineLine C, U)) :
    ∃ v : residueIndex.{u} p → Γ(affineLine C, U),
      ∑ i, (v i) ^ p * coordinateMap C U (X ^ (i.down : ℕ)) = m := by
  classical
  let e := AffineCartier.affineFrobeniusSectionIso C p U
  obtain ⟨w, hw⟩ := e.toLinearEquiv.surjective m
  refine ⟨fun i => w i, ?_⟩
  have hs : (show Γ(affineLine C, U) from
      e.hom.hom (∑ i : residueIndex.{u} p, Finsupp.single i (w i))) =
        ∑ i : residueIndex.{u} p,
          (show Γ(affineLine C, U) from e.hom.hom (Finsupp.single i (w i))) :=
    map_sum e.hom.hom _ _
  have hw' : (show Γ(affineLine C, U) from
      e.hom.hom (∑ i : residueIndex.{u} p, Finsupp.single i (w i))) = m :=
    (congrArg (fun q : residueIndex.{u} p →₀ Γ(affineLine C, U) =>
      (show Γ(affineLine C, U) from e.hom.hom q)) (Finsupp.univ_sum_single w)).trans hw
  have ht (i : residueIndex.{u} p) :
      (show Γ(affineLine C, U) from e.hom.hom (Finsupp.single i (w i))) =
        (w i) ^ p * coordinateMap C U (X ^ (i.down : ℕ)) := by
    cases i with
    | up i => exact AffineCartier.affineFrobeniusSectionIso_single C p U i (w ⟨i⟩)
  have hsum : (∑ i : residueIndex.{u} p,
      (show Γ(affineLine C, U) from e.hom.hom (Finsupp.single i (w i)))) =
        ∑ i : residueIndex.{u} p, (w i) ^ p * coordinateMap C U (X ^ (i.down : ℕ)) :=
    Finset.sum_congr rfl (fun i _ => ht i)
  exact hsum.symm.trans (hs.symm.trans hw')

private def localOperator (U : (affineLine C).Opens) (φ : localOperators (alpha C p) U)
    (V : Over U) : FrobeniusLinearMap Γ(affineLine C, V.left) p where
  toAddMonoidHom :=
    { toFun := fun m => (show Γ(affineLine C, V.left) from (φ.val.app (op V)).hom m)
      map_zero' := (φ.val.app (op V)).hom.map_zero
      map_add' := fun m n => (φ.val.app (op V)).hom.map_add m n }
  map_pow_mul' a b := by
    have h := (φ.val.app (op V)).hom.map_smul a b
    change (show Γ(affineLine C, V.left) from (φ.val.app (op V)).hom (a ^ p * b)) =
      a * (show Γ(affineLine C, V.left) from (φ.val.app (op V)).hom b) at h
    exact h

omit [PerfectRing C p] in
private theorem localOperator_res (U : (affineLine C).Opens)
    (φ : localOperators (alpha C p) U) (V : Over U) (m : Γ(affineLine C, U)) :
    localOperator C p U φ V ((affineLine C).presheaf.map V.hom.op m) =
      (affineLine C).presheaf.map V.hom.op
        (localOperator C p U φ (Over.mk (𝟙 U)) m) := by
  let k : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom (Category.comp_id _)
  exact PresheafOfModules.naturality_apply φ.val k.op m

private theorem localOperator_ext (U : (affineLine C).Opens)
    (φ ψ : localOperators (alpha C p) U)
    (h : ∀ i : Fin p,
      localOperator C p U φ (Over.mk (𝟙 U)) (coordinateMap C U (X ^ (i : ℕ))) =
        localOperator C p U ψ (Over.mk (𝟙 U)) (coordinateMap C U (X ^ (i : ℕ)))) :
    φ = ψ := by
  have hV (V : Over U) (i : Fin p) :
      localOperator C p U φ V (coordinateMap C V.left (X ^ (i : ℕ))) =
        localOperator C p U ψ V (coordinateMap C V.left (X ^ (i : ℕ))) := by
    have hr := coordinateMap_res C U V (X ^ (i : ℕ))
    have hφ := (congrArg (localOperator C p U φ V) hr).symm.trans
      (localOperator_res C p U φ V (coordinateMap C U (X ^ (i : ℕ))))
    have hψ := (congrArg (localOperator C p U ψ V) hr).symm.trans
      (localOperator_res C p U ψ V (coordinateMap C U (X ^ (i : ℕ))))
    exact hφ.trans ((congrArg
      (fun m : Γ(affineLine C, U) => (affineLine C).presheaf.map V.hom.op m)
      (h i)).trans hψ.symm)
  ext V m
  change localOperator C p U φ V.unop (show Γ(affineLine C, V.unop.left) from m) =
    localOperator C p U ψ V.unop (show Γ(affineLine C, V.unop.left) from m)
  obtain ⟨v, hv⟩ := section_expansion C p V.unop.left
    (show Γ(affineLine C, V.unop.left) from m)
  rw [← hv]
  change (localOperator C p U φ V.unop).toAddMonoidHom
      (∑ i, (v i) ^ p * coordinateMap C V.unop.left (X ^ (i.down : ℕ))) =
    (localOperator C p U ψ V.unop).toAddMonoidHom
      (∑ i, (v i) ^ p * coordinateMap C V.unop.left (X ^ (i.down : ℕ)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ((localOperator C p U φ V.unop).map_pow_mul (v i) _).trans
    ((congrArg (fun z => v i * z) (hV V.unop i.down)).trans
      ((localOperator C p U ψ V.unop).map_pow_mul (v i) _).symm)

private def trace : SchemeFrobeniusMap (affineLine C) p :=
  (univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p)

private def frameOperator (U : (affineLine C).Opens) (r : Γ(affineLine C, U)) :
    localOperators (alpha C p) U :=
  operatorModuleSections (alpha C p) U (((affineTraceFrame C p).val.app (op U)).hom r)

private theorem frameOperator_apply (U : (affineLine C).Opens)
    (r : Γ(affineLine C, U)) (V : Over U) (m : Γ(affineLine C, V.left)) :
    localOperator C p U (frameOperator C p U r) V m =
      (trace C p).onOpen V.left ((affineLine C).presheaf.map V.hom.op r * m) :=
  affineTraceFrame_apply C p U r V m

private theorem frameOperator_top (U : (affineLine C).Opens)
    (r m : Γ(affineLine C, U)) :
    localOperator C p U (frameOperator C p U r) (Over.mk (𝟙 U)) m =
      (trace C p).onOpen U (r * m) := by
  have h := frameOperator_apply C p U r (Over.mk (𝟙 U)) m
  have hi : (affineLine C).presheaf.map (𝟙 U).op r = r :=
    congrArg (fun f : Γ(affineLine C, U) ⟶ Γ(affineLine C, U) => f r)
      ((affineLine C).presheaf.map_id (op U))
  exact h.trans (congrArg (fun a : Γ(affineLine C, U) =>
    (trace C p).onOpen U (a * m)) hi)

private theorem trace_coordinate (U : (affineLine C).Opens) (f : Polynomial C) :
    (trace C p).onOpen U (coordinateMap C U f) =
      coordinateMap C U (univariateTrace (RingSplitting.ofPerfectRing C p) f) :=
  (univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec_constant
    (expChar_pos C p) U f

private theorem trace_pair (w : Fin p → Polynomial C)
    (hw : ∀ i j : Fin p,
      univariateTrace (RingSplitting.ofPerfectRing C p) (w i * X ^ (j : ℕ)) =
        if i = j then 1 else 0)
    (U : (affineLine C).Opens) (i j : Fin p) :
    (trace C p).onOpen U (coordinateMap C U (w i) * coordinateMap C U (X ^ (j : ℕ))) =
      if i = j then 1 else 0 := by
  have hm := congrArg ((trace C p).onOpen U)
    ((coordinateMap C U).map_mul (w i) (X ^ (j : ℕ))).symm
  have he : coordinateMap C U
      (univariateTrace (RingSplitting.ofPerfectRing C p) (w i * X ^ (j : ℕ))) =
        if i = j then 1 else 0 := by
    rw [hw]
    split_ifs <;> simp only [map_one, map_zero]
  exact hm.trans ((trace_coordinate C p U (w i * X ^ (j : ℕ))).trans he)

private theorem trace_reconstruct (w : Fin p → Polynomial C)
    (hw : ∀ i j : Fin p,
      univariateTrace (RingSplitting.ofPerfectRing C p) (w i * X ^ (j : ℕ)) =
        if i = j then 1 else 0)
    (U : (affineLine C).Opens) (a : Fin p → Γ(affineLine C, U)) (j : Fin p) :
    (trace C p).onOpen U
        ((∑ i, (a i) ^ p * coordinateMap C U (w i)) *
          coordinateMap C U (X ^ (j : ℕ))) = a j := by
  classical
  rw [Finset.sum_mul]
  change ((trace C p).onOpen U).toAddMonoidHom
    (∑ i, (a i) ^ p * coordinateMap C U (w i) *
      coordinateMap C U (X ^ (j : ℕ))) = a j
  rw [map_sum]
  have ht (i : Fin p) :
      (trace C p).onOpen U
          ((a i) ^ p * coordinateMap C U (w i) * coordinateMap C U (X ^ (j : ℕ))) =
        if i = j then a j else 0 := by
    rw [mul_assoc, FrobeniusLinearMap.map_pow_mul, trace_pair C p w hw]
    split_ifs with hij
    · subst i
      exact mul_one _
    · exact mul_zero _
  simp only [ht, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem trace_coordinates (w : Fin p → Polynomial C)
    (hw : ∀ i j : Fin p,
      univariateTrace (RingSplitting.ofPerfectRing C p) (w i * X ^ (j : ℕ)) =
        if i = j then 1 else 0)
    (U : (affineLine C).Opens) (v : residueIndex.{u} p → Γ(affineLine C, U))
    (i : Fin p) :
    (trace C p).onOpen U
        ((∑ j, (v j) ^ p * coordinateMap C U (X ^ (j.down : ℕ))) *
          coordinateMap C U (w i)) = v (ULift.up i) := by
  classical
  rw [Finset.sum_mul]
  change ((trace C p).onOpen U).toAddMonoidHom
    (∑ j, (v j) ^ p * coordinateMap C U (X ^ (j.down : ℕ)) *
      coordinateMap C U (w i)) = v (ULift.up i)
  rw [map_sum]
  have ht (j : residueIndex.{u} p) :
      (trace C p).onOpen U
          ((v j) ^ p * coordinateMap C U (X ^ (j.down : ℕ)) * coordinateMap C U (w i)) =
        if j = ULift.up i then v (ULift.up i) else 0 := by
    have hp := (congrArg ((trace C p).onOpen U)
      (mul_comm (coordinateMap C U (X ^ (j.down : ℕ))) (coordinateMap C U (w i)))).trans
      (trace_pair C p w hw U i j.down)
    rw [mul_assoc, FrobeniusLinearMap.map_pow_mul, hp]
    by_cases hj : j = ULift.up i
    · subst j
      simp
    · have hij : i ≠ j.down := by
        intro h
        apply hj
        exact ULift.ext h.symm
      simp only [hij, ite_false, hj, mul_zero]
  simp only [ht, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem frame_bijective (U : (affineLine C).Opens) :
    Function.Bijective (((affineTraceFrame C p).val.app (op U)).hom) := by
  classical
  obtain ⟨w, hw⟩ := exists_polynomialTrace_dual C p
  refine ⟨?_, ?_⟩
  · intro r s h
    obtain ⟨v, hv⟩ := section_expansion C p U (show Γ(affineLine C, U) from r)
    obtain ⟨z, hz⟩ := section_expansion C p U (show Γ(affineLine C, U) from s)
    have ho : frameOperator C p U r = frameOperator C p U s :=
      congrArg (operatorModuleSections (alpha C p) U) h
    have hi (i : Fin p) : v (ULift.up i) = z (ULift.up i) := by
      have hh := congrArg
        (fun φ : localOperators (alpha C p) U =>
          localOperator C p U φ (Over.mk (𝟙 U)) (coordinateMap C U (w i))) ho
      have ht := (frameOperator_top C p U r (coordinateMap C U (w i))).symm.trans
        (hh.trans (frameOperator_top C p U s (coordinateMap C U (w i))))
      have hr := (congrArg
        (fun q : Γ(affineLine C, U) =>
          (trace C p).onOpen U (q * coordinateMap C U (w i))) hv).symm.trans
        (trace_coordinates C p w hw U v i)
      have hs := (congrArg
        (fun q : Γ(affineLine C, U) =>
          (trace C p).onOpen U (q * coordinateMap C U (w i))) hz).symm.trans
        (trace_coordinates C p w hw U z i)
      exact hr.symm.trans (ht.trans hs)
    have hvz : v = z := by
      funext i
      cases i with
      | up i => exact hi i
    exact hv.symm.trans ((congrArg
      (fun a : residueIndex.{u} p → Γ(affineLine C, U) =>
        ∑ i, (a i) ^ p * coordinateMap C U (X ^ (i.down : ℕ))) hvz).trans hz)
  · intro φ
    let Φ := operatorModuleSections (alpha C p) U φ
    let a : Fin p → Γ(affineLine C, U) := fun i =>
      localOperator C p U Φ (Over.mk (𝟙 U)) (coordinateMap C U (X ^ (i : ℕ)))
    let r : Γ(affineLine C, U) := ∑ i, (a i) ^ p * coordinateMap C U (w i)
    refine ⟨r, ?_⟩
    apply (operatorModuleSections (alpha C p) U).injective
    change frameOperator C p U r = Φ
    apply localOperator_ext C p U
    intro j
    exact (frameOperator_top C p U r (coordinateMap C U (X ^ (j : ℕ)))).trans
      (trace_reconstruct C p w hw U a j)

/-- Weighted canonical trace identifies the structure sheaf with all local linear operators. -/
theorem affineTraceFrame_isIso : IsIso (affineTraceFrame C p) := by
  let M : (affineLine C).Modules := SheafOfModules.unit (affineLine C).ringCatSheaf
  let N : (affineLine C).Modules := operatorModule (alpha C p)
  let t : M ⟶ N := affineTraceFrame C p
  let (U : (affineLine C).Opensᵒᵖ) : IsIso (t.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (frame_bijective C p U.unop)
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun U => asIso (t.val.app U)) (fun {_ _} f => t.val.naturality f)
  have he : e.hom = t.val := by ext U; rfl
  let q : M ≅ N :=
    (SheafOfModules.fullyFaithfulForget (affineLine C).ringCatSheaf).preimageIso e
  have hq : q.hom = t :=
    (SheafOfModules.fullyFaithfulForget (affineLine C).ringCatSheaf).map_injective (X := M) (Y := N)
      (((SheafOfModules.fullyFaithfulForget (affineLine C).ringCatSheaf).map_preimage
        (X := M) (Y := N) e.hom).trans he)
  have ht : IsIso t := hq ▸ q.isIso_hom
  exact ht

end FrobeniusSplitting.OperatorSheaf
