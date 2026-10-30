import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionRadical
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootIntersection
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOpposite

/-! # The root unipotent subgroup is the Borel unipotent radical -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem empty_points : standardParabolicPoints G ∅ = G.borelPoints := by
  simp only [standardParabolicPoints, Set.image_empty, Subgroup.closure_empty, sup_bot_eq]

private instance borelReduced :
    IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj G.borelIdeal) := by
  change IsReduced G.borelAlgebra
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact isReduced_of_smooth K G.borelAlgebra

private theorem empty_ideal :
    HopfIdeal.vanishingIdeal (standardParabolicPoints G ∅) = G.borelIdeal := by
  rw [empty_points]
  apply le_antisymm
  · apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
    exact (HopfIdeal.le_vanishingIdeal_iff G.borelPoints
      (HopfIdeal.vanishingIdeal G.borelPoints)).mp le_rfl
  · exact (HopfIdeal.le_vanishingIdeal_iff G.borelPoints G.borelIdeal).mpr le_rfl

private theorem empty_roots :
    parabolicRadicalRoots G.rootBase ∅ = {r | G.rootBase.IsPos r} := by
  have he : leviPositiveRoots G.rootBase ∅ = ∅ := by
    ext r
    simp [leviPositiveRoots]
  ext r
  simp only [parabolicRadicalRoots, he, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, not_false_eq_true, and_true]

private theorem full_ideal :
    G.rootSubsetIdeal {r | G.rootBase.IsPos r} (isPositiveRootClosed_isPos G.rootBase) =
      G.unipotentIdeal := by
  let : IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj G.unipotentIdeal) := by
    change IsReduced G.unipotentAlgebra
    let : Algebra.Smooth K G.unipotentAlgebra := G.unipotent_smooth
    exact isReduced_of_smooth K G.unipotentAlgebra
  let : IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj
      (G.rootSubsetIdeal {r | G.rootBase.IsPos r}
        (isPositiveRootClosed_isPos G.rootBase))) := by
    change IsReduced (G.rootSubsetAlgebra {r | G.rootBase.IsPos r}
      (isPositiveRootClosed_isPos G.rootBase))
    infer_instance
  apply HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := K)
  exact G.fullRootPoints_eq_unipotent

private instance rootReduced (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) :
    IsReduced (CommHopfAlgCat.quotient G.coordinateAlgebra.obj (G.rootSubsetIdeal R hR)) := by
  change IsReduced (G.rootSubsetAlgebra R hR)
  infer_instance

private theorem parabolic_le_root (I : Set G.rootBase.support) :
    HopfIdeal.vanishingIdeal (standardParabolicPoints G I) ≤
      G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
        (parabolicRadicalRoots_closed G.rootBase I) := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro g hg
  apply (HopfIdeal.le_vanishingIdeal_iff (standardParabolicPoints G I)
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))).mp le_rfl
  rw [parabolic_eq_levi_sup_unipotent]
  exact (show parabolicUnipotentPoints G I ≤ _ from le_sup_right) hg

private def ambientRadical (J : HopfIdeal K G.coordinateAlgebra) :
    HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.comapOfSurjective
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra J))
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj J).hom
    (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj J)

/-- Pulling the parabolic unipotent radical into the ambient group gives its root-support ideal. -/
theorem parabolicRadical_ambient (I : Set G.rootBase.support) :
    HopfIdeal.comapOfSurjective
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (parabolicAlgebra G I))
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj
          (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))).hom
        (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj _) =
      G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
        (parabolicRadicalRoots_closed G.rootBase I) := by
  rw [← parabolicUnipotent_isRadical G I]
  ext x
  simp only [HopfIdeal.mem_comapOfSurjective, parabolicUnipotentIdeal,
    HopfIdeal.mem_kerOfSurjective]
  change (CommHopfAlgCat.quotientMapOfLe G.coordinateAlgebra.obj
    (parabolic_le_root G I)).hom
      (Ideal.Quotient.mkₐ K (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)).toIdeal x) =
        0 ↔ x ∈ G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
          (parabolicRadicalRoots_closed G.rootBase I)
  rw [CommHopfAlgCat.quotientMapOfLe_mk]
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem ideal_congr {R S : Set G.rootIndex}
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (h : R = S) : G.rootSubsetIdeal R hR = G.rootSubsetIdeal S hS := by
  subst S
  rfl

/-- The canonical Borel radical has the ambient defining ideal of the root unipotent subgroup. -/
theorem borelRadical_ambient :
    HopfIdeal.comapOfSurjective
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.borelAlgebra)
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom
        (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj G.borelIdeal) =
      G.unipotentIdeal := by
  have h := parabolicRadical_ambient G ∅
  have he := congrArg (ambientRadical G) (empty_ideal G)
  exact he.symm.trans
    (h.trans ((ideal_congr G _ _ (empty_roots G)).trans (full_ideal G)))

/-- Inside the Borel coordinate algebra, the root unipotent ideal is the radical ideal. -/
theorem borelUnipotent_isRadical :
    G.unipotentIdeal.map (Bialgebra.Quotient.mkBialgHom G.borelIdeal.toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.borelAlgebra := by
  apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom
    (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj G.borelIdeal)).mp
  exact (HopfIdeal.comapOfSurjective_map_mkQuotient
    G.borel_le_unipotentIdeal).trans (borelRadical_ambient G).symm
omit [IsAlgClosed K] [CharZero K] in
private abbrev ambientR (H : FiniteTypeCommHopfAlgCat.{u, u} K) (I : HopfIdeal K H) :
    HopfIdeal K H :=
  HopfIdeal.comapOfSurjective
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.quotient H I))
    (CommHopfAlgCat.mkQuotient H.obj I).hom
    (CommHopfAlgCat.mkQuotient_surjective H.obj I)

omit [IsAlgClosed K] [CharZero K] in
private theorem ambientR_iso (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (I : HopfIdeal K H) (e : H ≅ H) :
    ambientR H (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom).2) =
      (ambientR H I).comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
  let J := I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  let q := FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I
  have hr := FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal q
  have hc := FiniteTypeCommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom e I
  ext x
  simp only [ambientR, HopfIdeal.mem_comapOfSurjective]
  change (FiniteTypeCommHopfAlgCat.toBialgHom
      (FiniteTypeCommHopfAlgCat.mkQuotient H J)) x ∈
        FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient H J) ↔ _
  rw [← hr]
  simp only [HopfIdeal.mem_comapOfSurjective]
  have hx := congrArg (fun f : H ⟶ FiniteTypeCommHopfAlgCat.quotient H I =>
    FiniteTypeCommHopfAlgCat.toBialgHom f x) hc
  have hq : FiniteTypeCommHopfAlgCat.toBialgHom
      (FiniteTypeCommHopfAlgCat.mkQuotient H I) =
      (CommHopfAlgCat.mkQuotient H.obj I).hom := by
    ext a
    rfl
  simpa only [q, J, FiniteTypeCommHopfAlgCat.toBialgHom_comp, BialgHom.comp_apply, hq] using
    (Iff.of_eq (congrArg (fun z => z ∈
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
        (FiniteTypeCommHopfAlgCat.quotient H I)) hx))

omit [IsAlgClosed K] [CharZero K] in
private theorem ambientR_conjugate (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (I : HopfIdeal K H) (g : WithConv (H →ₐ[K] K)) :
    ambientR H (I.conjugate g) = (ambientR H I).conjugate g := by
  let e : H ≅ H := ObjectProperty.isoMk _ <|
    (CommHopfAlgCat.ofIsoSelf H.obj).symm ≪≫
      CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g) ≪≫
      CommHopfAlgCat.ofIsoSelf H.obj
  have he : FiniteTypeCommHopfAlgCat.toBialgHom e.hom =
      (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom := by
    ext a
    rfl
  simpa only [HopfIdeal.conjugate_eq_comapOfSurjective, he] using ambientR_iso H I e


/-- The opposite Borel radical has the ambient ideal of the opposite unipotent subgroup. -/
theorem oppositeBorelRadical_ambient :
    HopfIdeal.comapOfSurjective
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.oppositeBorelAlgebra)
        (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.oppositeBorelIdeal).hom
        (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj G.oppositeBorelIdeal) =
      G.oppositeUnipotentIdeal := by
  change ambientR G.coordinateAlgebra (G.borelIdeal.conjugate G.longestPoint) =
    G.unipotentIdeal.conjugate G.longestPoint
  rw [ambientR_conjugate]
  exact congrArg (fun I : HopfIdeal K G.coordinateAlgebra => I.conjugate G.longestPoint)
    (borelRadical_ambient G)

/-- Inside the opposite Borel, the opposite root unipotent ideal is the radical ideal. -/
theorem oppositeUnipotent_isRadical :
    G.oppositeUnipotentIdeal.map
      (Bialgebra.Quotient.mkBialgHom G.oppositeBorelIdeal.toIdeal) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G.oppositeBorelAlgebra := by
  apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.oppositeBorelIdeal).hom
    (CommHopfAlgCat.mkQuotient_surjective G.coordinateAlgebra.obj G.oppositeBorelIdeal)).mp
  exact (HopfIdeal.comapOfSurjective_map_mkQuotient
    (HopfIdeal.conjugate_mono G.longestPoint G.borel_le_unipotentIdeal)).trans
      (oppositeBorelRadical_ambient G).symm

end
end SchubertGeometry
