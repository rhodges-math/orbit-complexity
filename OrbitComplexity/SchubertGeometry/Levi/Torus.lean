import OrbitComplexity.SchubertGeometry.Levi.Connected
import OrbitComplexity.SchubertGeometry.Levi.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-! # The chosen maximal torus in a standard Levi

The ambient torus quotient descends through the Levi coordinate algebra.
Its maximality follows by pulling any containing torus back to the ambient group.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions TauCeti CategoryTheory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem levi_le_torus (I : Set G.rootBase.support) : G.leviIdeal I ≤ G.torusIdeal :=
  (G.leviIdeal_le_leviBorel I).trans (G.leviBorelIdeal_le_torus I)

private def torusMap (I : Set G.rootBase.support) :
    (G.leviAlgebra I).obj ⟶ G.torusAlgebra.obj :=
  CommHopfAlgCat.quotientMapOfLe (CommHopfAlgCat.of K G.coordinateAlgebra) (levi_le_torus G I)

private theorem torusMap_surjective (I : Set G.rootBase.support) :
    Function.Surjective (torusMap G I).hom :=
  CommHopfAlgCat.quotientMapOfLe_surjective _ (levi_le_torus G I)

/-- The defining ideal of the chosen torus inside the standard Levi coordinate algebra. -/
def leviTorusIdeal (I : Set G.rootBase.support) : HopfIdeal K (G.leviAlgebra I) :=
  HopfIdeal.kerOfSurjective (torusMap G I).hom (torusMap_surjective G I)

/-- The torus quotient inside the Levi is the original torus coordinate Hopf algebra. -/
def leviTorusQuotientIso (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotient (G.leviAlgebra I).obj (leviTorusIdeal G I) ≅ G.torusAlgebra.obj :=
  CommHopfAlgCat.quotientKerOfSurjectiveIso (torusMap G I) (torusMap_surjective G I)

private theorem torusIdeal_eq_map (I : Set G.rootBase.support) :
    leviTorusIdeal G I = G.torusIdeal.map
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra) (G.leviIdeal I)).hom :=
  CommHopfAlgCat.kerOfSurjective_quotientMapOfLe _ (levi_le_torus G I)

/-- The chosen torus is contained in the Levi--Borel subgroup of the Levi. -/
theorem leviBorel_le_torus (I : Set G.rootBase.support) :
    leviBorelIdealInLevi G I ≤ leviTorusIdeal G I := by
  have hb : leviBorelIdealInLevi G I = (G.leviBorelIdeal I).map
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra)
        (G.leviIdeal I)).hom :=
    CommHopfAlgCat.kerOfSurjective_quotientMapOfLe _ (G.leviIdeal_le_leviBorel I)
  rw [hb, torusIdeal_eq_map]
  exact HopfIdeal.map_mono _ (G.leviBorelIdeal_le_torus I)

private theorem torusIdeal_comap (I : Set G.rootBase.support) :
    (leviTorusIdeal G I).comapOfSurjective
        (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra)
          (G.leviIdeal I)).hom (CommHopfAlgCat.mkQuotient_surjective _ _) = G.torusIdeal := by
  rw [torusIdeal_eq_map]
  exact HopfIdeal.comapOfSurjective_map_mkQuotient (levi_le_torus G I)

private theorem torus_property (I : Set G.rootBase.support) :
    torusCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient
      (G.leviAlgebra I) (leviTorusIdeal G I)) := by
  let e : FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) (leviTorusIdeal G I) ≅
      G.torusAlgebra := ObjectProperty.isoMk _ (leviTorusQuotientIso G I)
  exact (torusCommHopfAlgProperty K).prop_of_iso e.symm G.torus_isTorus

/-- The chosen ambient torus remains maximal in the standard Levi subgroup. -/
theorem leviTorus_isMaximal (I : Set G.rootBase.support) :
    HopfIdeal.IsMaximalTorus K (G.leviAlgebra I).obj (leviTorusIdeal G I) := by
  refine ⟨torus_property G I, ?_⟩
  intro J hJ hJI
  let q := CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K G.coordinateAlgebra) (G.leviIdeal I)
  let hq := CommHopfAlgCat.mkQuotient_surjective
    (CommHopfAlgCat.of K G.coordinateAlgebra) (G.leviIdeal I)
  let J₀ := J.comapOfSurjective q.hom hq
  have hJ₀ : torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra J₀) := by
    let e : FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra J₀ ≅
        FiniteTypeCommHopfAlgCat.quotient (G.leviAlgebra I) J :=
      ObjectProperty.isoMk _ (CommHopfAlgCat.quotientIsoOfSurjective q hq J)
    exact (torusCommHopfAlgProperty K).prop_of_iso e.symm hJ
  have hJT : J₀ ≤ G.torusIdeal := by
    rw [← torusIdeal_comap G I]
    exact HopfIdeal.comapOfSurjective_mono q.hom hq hJI
  have hTJ : G.torusIdeal ≤ J₀ := G.isMaximalTorus.2 hJ₀ hJT
  rw [torusIdeal_eq_map]
  have hm := HopfIdeal.map_mono q.hom hTJ
  exact hm.trans_eq (HopfIdeal.map_comapOfSurjective _ _ hq)

/-- Restriction of functions from the Levi to the original split torus. -/
def leviTorusSplit (I : Set G.rootBase.support) :
    G.leviAlgebra I →ₐc[K] MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) :=
  Bialgebra.Quotient.liftBialgHom (G.leviIdeal I).toIdeal G.torusSplit
    (fun a ha => (G.split_eq_zero a).mpr (levi_le_torus G I ha))

/-- Restriction from the Levi to its split torus is surjective. -/
theorem leviTorusSplit_surjective (I : Set G.rootBase.support) :
    Function.Surjective (leviTorusSplit G I) := by
  intro y
  obtain ⟨a, ha⟩ := G.split_surjective y
  refine ⟨Ideal.Quotient.mkₐ K (G.leviIdeal I).toIdeal a, ?_⟩
  change G.torusSplit a = y
  exact ha

/-- The descended splitting has kernel equal to the defining torus ideal inside the Levi. -/
theorem leviTorusSplit_eq_zero (I : Set G.rootBase.support) (a : G.leviAlgebra I) :
    leviTorusSplit G I a = 0 ↔ a ∈ (leviTorusIdeal G I).toIdeal := by
  refine Quotient.inductionOn' a ?_
  intro a
  change G.torusSplit a = 0 ↔ Ideal.Quotient.mk G.torusIdeal.toIdeal a = 0
  rw [G.split_eq_zero, Ideal.Quotient.eq_zero_iff_mem]

end SchubertGeometry
