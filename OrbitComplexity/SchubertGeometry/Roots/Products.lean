import OrbitComplexity.SchubertGeometry.Roots.Containment
import OrbitComplexity.SchubertGeometry.Roots.Conjugation
import OrbitComplexity.GroupActions.Varieties.RootOrderedProduct

/-! # Ordered multiplication of the canonical root subgroups -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev factorRoot (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    G.rootIndex :=
  G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i)

private theorem factor_tangent
    (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    gaAffineGroupTangent (G.borelRootMaps i) ∈ G.rootWeightSpace (factorRoot G i) ∧
      gaAffineGroupTangent (G.borelRootMaps i) ≠ 0 := by
  constructor
  · have hc : G.rootCharacter (factorRoot G i) = i.val := by
      change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val
      rw [Equiv.symm_apply_apply]
      rfl
    change _ ∈ affineGroupCharacterWeightSpace G.torusSplit (G.rootCharacter _)
    rw [hc]
    exact G.borelRootMaps_weight i
  · rw [← G.borelRootBasis_tangent i]
    intro h
    exact G.borelRootBasis.ne_zero i (Subtype.ext h)

private def factorEquiv (i : borelRootCharacterIndex G.borelIdeal G.torusSplit) :
    K ≃ rootSubgroupPoints G (factorRoot G i) :=
  Equiv.ofBijective (fun a => ⟨gaParameterPoint (G.borelRootMaps i) a, by
    change _ ∈ (rootSubgroupPoints G (factorRoot G i) : Set G.points)
    rw [← rootSubgroupPoints_eq_range G _ _ (factor_tangent G i).1
      (factor_tangent G i).2]
    exact ⟨a, rfl⟩⟩) ⟨by
      intro a b h
      exact congrArg Multiplicative.toAdd
        (GaAffineGroupPoints.injective_of_tangent_ne_zero (G.borelRootMaps i)
          (factor_tangent G i).2 (congrArg Subtype.val h)), by
      intro g
      have hg := g.property
      change g.val ∈ (rootSubgroupPoints G (factorRoot G i) : Set G.points) at hg
      rw [← rootSubgroupPoints_eq_range G _ _ (factor_tangent G i).1
        (factor_tangent G i).2] at hg
      obtain ⟨a, ha⟩ := hg
      exact ⟨a, Subtype.ext ha⟩⟩

/-- In every order, canonical root-group factors multiply uniquely to the closed support. -/
theorem rootSupport_directly_spanned (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (l : List (G.rootCharacters R)) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (∀ u : (i : G.rootCharacters R) → rootSubgroupPoints G
        (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
      (l.map (fun i => (u i : G.points))).prod ∈ G.rootSubsetPoints R hR) ∧
    ∀ g : G.points, g ∈ G.rootSubsetPoints R hR →
      ∃! u : (i : G.rootCharacters R) → rootSubgroupPoints G
          (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)),
        (l.map (fun i => (u i : G.points))).prod = g := by
  let e : (G.rootCharacters R → K) ≃
      ((i : G.rootCharacters R) → rootSubgroupPoints G (factorRoot G i.val)) :=
    Equiv.piCongrRight (fun i => factorEquiv G i.val)
  have he (a : G.rootCharacters R → K) :
      (l.map (fun i => (e a i : G.points))).prod =
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod := rfl
  obtain ⟨hmem, huniq⟩ := rootSubset_ordered_product G R hR l hl hall
  constructor
  · intro u
    obtain ⟨a, rfl⟩ := e.surjective u
    rw [he]
    exact hmem a
  · intro g hg
    obtain ⟨a, ha, huni⟩ := huniq g hg
    refine ⟨e a, (he a).trans ha, ?_⟩
    intro u hu
    obtain ⟨b, rfl⟩ := e.surjective u
    exact congrArg e (huni b ((he b).symm.trans hu))

/-- Every ordered subgroup chart multiplies factors in the canonical root groups. -/
theorem rootSupport_chart_factors (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (l : List (G.rootCharacters R)) (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (∀ i : G.rootCharacters R,
      Set.range (fun a : K => gaParameterPoint (G.borelRootMaps i.val) a) =
        (rootSubgroupPoints G (G.characterRootEquiv
          (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)) : Set G.points)) ∧
    ∀ a : G.rootCharacters R → K,
      (rootSubsetPointsMulEquiv G R hR
        (Variety.mapPoints (rootSubsetProductChart G R hR l hl hall).hom
          ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
        (l.map (fun i => gaParameterPoint (G.borelRootMaps i.val) (a i))).prod :=
  ⟨fun i => rootSubgroupPoints_eq_range G _ _ (factor_tangent G i.val).1
    (factor_tangent G i.val).2, rootSubsetProductChart_points G R hR l hl hall⟩

private theorem mapped_direct_span {M ι : Type*} [Group M]
    (P Q : Subgroup M) (S T : ι → Subgroup M) (l : List ι) (e : M ≃* M)
    (hP : P.map e.toMonoidHom = Q) (hS : ∀ i, (S i).map e.toMonoidHom = T i)
    (h : (∀ u : (i : ι) → S i, (l.map (fun i => (u i : M))).prod ∈ P) ∧
      ∀ g : M, g ∈ P → ∃! u : (i : ι) → S i,
        (l.map (fun i => (u i : M))).prod = g) :
    (∀ u : (i : ι) → T i, (l.map (fun i => (u i : M))).prod ∈ Q) ∧
      ∀ g : M, g ∈ Q → ∃! u : (i : ι) → T i,
        (l.map (fun i => (u i : M))).prod = g := by
  let F : ((i : ι) → S i) ≃ ((i : ι) → T i) := Equiv.piCongrRight fun i =>
    ((S i).equivMapOfInjective e.toMonoidHom e.injective).toEquiv.trans
      (MulEquiv.subgroupCongr (hS i)).toEquiv
  have hF (u : (i : ι) → S i) :
      (l.map (fun i => (F u i : M))).prod = e ((l.map (fun i => (u i : M))).prod) := by
    change (l.map (fun i => e (u i))).prod = _
    simpa only [List.map_map, Function.comp_def] using
      (map_list_prod e (l.map (fun i => (u i : M)))).symm
  constructor
  · intro v
    obtain ⟨u, rfl⟩ := F.surjective v
    rw [hF, ← hP]
    exact Subgroup.mem_map.mpr ⟨_, h.1 u, rfl⟩
  · intro g hg
    have hgP : e.symm g ∈ P := by
      rw [← hP] at hg
      exact Subgroup.mem_map_equiv.mp hg
    obtain ⟨u, hu, huniq⟩ := h.2 (e.symm g) hgP
    refine ⟨F u, (hF u).trans ((congrArg e hu).trans (e.apply_symm_apply g)), ?_⟩
    intro v hv
    obtain ⟨a, rfl⟩ := F.surjective v
    apply congrArg F
    apply huniq
    apply e.injective
    exact (hF a).symm.trans (hv.trans (e.apply_symm_apply g).symm)


private theorem longest_unipotent :
    G.unipotentPoints.map (MulAut.conj G.longestPoint).toMonoidHom =
      G.oppositeUnipotentPoints := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (G.conj_mem_oppositeUnipotent a).mpr ha
  · intro hg
    let a := G.longestPoint⁻¹ * g * G.longestPoint
    have he : G.longestPoint * a * G.longestPoint⁻¹ = g := by dsimp [a]; group
    refine ⟨a, (G.conj_mem_oppositeUnipotent a).mp (he.symm ▸ hg), he⟩

/-- In every order, the transported negative root groups directly span the opposite group. -/
theorem opposite_directly_spanned
    (l : List (G.rootCharacters {r | G.rootBase.IsPos r}))
    (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (∀ u : (i : G.rootCharacters {r | G.rootBase.IsPos r}) →
        rootSubgroupPoints G (G.rootSystem.weylGroupToPerm G.longestElement
          (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val))),
      (l.map (fun i => (u i : G.points))).prod ∈ G.oppositeUnipotentPoints) ∧
    ∀ g : G.points, g ∈ G.oppositeUnipotentPoints →
      ∃! u : (i : G.rootCharacters {r | G.rootBase.IsPos r}) →
          rootSubgroupPoints G (G.rootSystem.weylGroupToPerm G.longestElement
            (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val))),
        (l.map (fun i => (u i : G.points))).prod = g := by
  have h := rootSupport_directly_spanned G {r | G.rootBase.IsPos r}
    (isPositiveRootClosed_isPos G.rootBase) l hl hall
  rw [G.fullRootPoints_eq_unipotent] at h
  exact mapped_direct_span G.unipotentPoints G.oppositeUnipotentPoints
    (fun i : G.rootCharacters {r | G.rootBase.IsPos r} => rootSubgroupPoints G
      (G.characterRootEquiv (borelRootCharacterOccurring G.borelIdeal G.torusSplit i.val)))
    _ l (MulAut.conj G.longestPoint) (longest_unipotent G)
    (fun i => rootSubgroup_weyl_conjugate G G.longestElement _) h

end
end SchubertGeometry
