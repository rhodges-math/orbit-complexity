import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.PrincipalCharts
import OrbitComplexity.FrobeniusSplitting.Normality.LocalizationMaps
import OrbitComplexity.FrobeniusSplitting.Normality.AffineOpenMaps

/-!
# Open images of principal diagrams

The preserved principal patch graph identifies coefficient-model maps as open immersions.
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

namespace PrincipalDiagram

variable {C : Type v} [Category.{w} C] {K : Type u} [CommRing K]
    {S : Subalgebra ℤ K} (D₀ : C ⥤ CommAlgCat.{u} S) (D : C ⥤ CommAlgCat.{u} K)
    (L : DiagramArrow C → Type u)
    (g : ∀ b, L b → D₀.obj b.1) (a : ∀ b, L b → D.obj b.1)

/-- A generic graph arrow restricts to its preserved coefficient-model subalgebras. -/
def imageMap {R : Subalgebra ℤ K}
    (models : ∀ n, Subalgebra R (genericAt D L a n))
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
      maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b))
    (b : PrincipalEdge L) : models (edgeSrc L b) →ₐ[R] models (edgeTgt L b) :=
  (((maps b).restrictScalars R).comp (models (edgeSrc L b)).val).codRestrict
    (models (edgeTgt L b)) (fun x ↦ preserve b x)

private theorem imageMap_bijective {R : Subalgebra ℤ K}
    (models : ∀ n, Subalgebra R (genericAt D L a n))
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
      maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b))
    (b : DiagramArrow C) (j : L b)
    (e : Localization.Away (a b j) ≃ₐ[K]
      Localization.Away ((D.map b.2.2).hom (a b j)))
    (hforward : maps (.inr (⟨b, j⟩, .inr false)) = e.toAlgHom)
    (hbackward : maps (.inr (⟨b, j⟩, .inr true)) = e.symm.toAlgHom) :
    Function.Bijective (imageMap D L a models maps preserve (.inr (⟨b, j⟩, .inr false))) := by
  let f := imageMap D L a models maps preserve (.inr (⟨b, j⟩, .inr false))
  have hf (x : models (.inr (⟨b, j⟩, false))) :
      (f x).val = e x.val := AlgHom.congr_fun hforward x.val
  have hinv (y : models (.inr (⟨b, j⟩, true))) :
      e.symm y.val ∈ models (.inr (⟨b, j⟩, false)) := by
    have hy := preserve (.inr (⟨b, j⟩, .inr true)) y
    have h := AlgHom.congr_fun hbackward y.val
    exact h ▸ hy
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact (hf x).symm.trans ((congrArg Subtype.val hxy).trans (hf y))
  · intro y
    let x : models (.inr (⟨b, j⟩, false)) := ⟨e.symm y.val, hinv y⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact (hf x).trans (e.apply_symm_apply y.val)

private theorem imageArrow_away_bijective {R : Subalgebra ℤ K}
    [Algebra S R] [IsScalarTower S R K]
    (e : ∀ i, K ⊗[S] D₀.obj i ≃ₐ[K] D.obj i)
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    (hg : ∀ b j, e b.1 ((1 : K) ⊗ₜ[S] g b j) = a b j)
    (models : ∀ n, Subalgebra R (genericAt D L a n))
    (hintrinsic : ∀ n, models n = (scalarImageHom (R := R)
      (localizationComparisons D₀ D L g a e hnatural hg n)).range)
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
      maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b))
    (b : DiagramArrow C) (j : L b)
    (hbase : maps (.inl b) = (D.map b.2.2).hom)
    (hlocal : Function.Bijective
      (Localization.awayMap (D.map b.2.2).hom.toRingHom (a b j)))
    (hforward : maps (.inr (⟨b, j⟩, .inr false)) =
      Localization.awayMapₐ (D.map b.2.2).hom (a b j))
    (hbackward : maps (.inr (⟨b, j⟩, .inr true)) =
      (AlgEquiv.ofBijective (Localization.awayMapₐ (D.map b.2.2).hom (a b j))
        hlocal).symm.toAlgHom) :
    ∃ ha : a b j ∈ models (.inl b.1),
      Function.Bijective (Localization.awayMap
        (imageMap D L a models maps preserve (.inl b)).toRingHom
        (⟨a b j, ha⟩ : models (.inl b.1))) := by
  classical
  have hmodels : models = fun n ↦ (scalarImageHom (R := R)
      (localizationComparisons D₀ D L g a e hnatural hg n)).range := funext hintrinsic
  cases hmodels
  let qS := scalarImageHom (R := R) (e b.1)
  let qT := scalarImageHom (R := R) (e b.2.1)
  let gT := (D₀.map b.2.2).hom (g b j)
  have hgT : e b.2.1 ((1 : K) ⊗ₜ[S] gT) = (D.map b.2.2).hom (a b j) := by
    have h := AlgHom.congr_fun (hnatural b.1 b.2.1 b.2.2) ((1 : K) ⊗ₜ[S] g b j)
    change e b.2.1 ((1 : K) ⊗ₜ[S] gT) =
      (D.map b.2.2).hom (e b.1 ((1 : K) ⊗ₜ[S] g b j)) at h
    exact h.trans (congrArg (D.map b.2.2).hom (hg b j))
  let dS := localizationScalarEquiv (B := Localization.Away (a b j))
    (e b.1) (g b j) (a b j) (hg b j)
  let dT := localizationScalarEquiv
    (B := Localization.Away ((D.map b.2.2).hom (a b j)))
      (e b.2.1) gT ((D.map b.2.2).hom (a b j)) hgT
  let rS := scalarImageHom (R := R) dS
  let rT := scalarImageHom (R := R) dT
  have : IsScalarTower R (D.obj b.1) (Localization.Away (a b j)) :=
    IsScalarTower.to₁₃₄ R K (D.obj b.1) (Localization.Away (a b j))
  have : IsScalarTower R (D.obj b.2.1)
      (Localization.Away ((D.map b.2.2).hom (a b j))) :=
    IsScalarTower.to₁₃₄ R K (D.obj b.2.1) _
  obtain ⟨fS, hfS, hlocS⟩ := scalarImage_localization (R := R)
    (e b.1) dS (g b j) (localizationScalarEquiv_tmul _ _ _ _)
  obtain ⟨fT, hfT, hlocT⟩ := scalarImage_localization (R := R)
    (e b.2.1) dT gT (localizationScalarEquiv_tmul _ _ _ _)
  let model := fun n ↦ (scalarImageHom (R := R)
    (localizationComparisons D₀ D L g a e hnatural hg n)).range
  let f₀ : qS.range →ₐ[R] qT.range := imageMap D L a model maps preserve (.inl b)
  let ψ : rS.range →ₐ[R] rT.range :=
    imageMap D L a model maps preserve (.inr (⟨b, j⟩, .inr false))
  let E := AlgEquiv.ofBijective (Localization.awayMapₐ (D.map b.2.2).hom (a b j)) hlocal
  have hψ : Function.Bijective ψ :=
    imageMap_bijective D L a model maps preserve b j E hforward hbackward
  let zS : qS.range := ⟨qS ((1 : R) ⊗ₜ[S] g b j), ⟨(1 : R) ⊗ₜ[S] g b j, rfl⟩⟩
  let zT : qT.range := ⟨qT ((1 : R) ⊗ₜ[S] gT), ⟨(1 : R) ⊗ₜ[S] gT, rfl⟩⟩
  have hzS : zS.val = a b j := by
    change (e b.1).toAlgHom ((algebraMap R K 1) ⊗ₜ[S] g b j) = a b j
    rw [map_one]
    exact hg b j
  have hzT : zT.val = (D.map b.2.2).hom (a b j) := by
    change (e b.2.1).toAlgHom ((algebraMap R K 1) ⊗ₜ[S] gT) = _
    rw [map_one]
    exact hgT
  have hz : zT = f₀ zS := by
    apply Subtype.ext
    have h := AlgHom.congr_fun hbase zS.val
    exact hzT.trans ((congrArg (D.map b.2.2).hom hzS).symm.trans h.symm)
  let : Algebra qS.range rS.range := fS.toAlgebra
  let : Algebra qT.range rT.range := fT.toAlgebra
  have : IsLocalization.Away zS rS.range := hlocS
  have : IsLocalization.Away (f₀ zS) rT.range := hz ▸ hlocT
  have hcomm : ψ.toRingHom.comp (algebraMap qS.range rS.range) =
      (algebraMap qT.range rT.range).comp f₀.toRingHom := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    change (ψ (fS x)).val = (fT (f₀ x)).val
    calc
      (ψ (fS x)).val = E (fS x).val := AlgHom.congr_fun hforward (fS x).val
      _ = E (algebraMap (D.obj b.1) (Localization.Away (a b j)) x.val) :=
        congrArg E (hfS x)
      _ = algebraMap (D.obj b.2.1) (Localization.Away ((D.map b.2.2).hom (a b j)))
          ((D.map b.2.2).hom x.val) := by
        change IsLocalization.Away.map _ _ (D.map b.2.2).hom.toRingHom (a b j)
          (algebraMap (D.obj b.1) (Localization.Away (a b j)) x.val) = _
        simp only [IsLocalization.Away.map, IsLocalization.map_eq]
        rfl
      _ = algebraMap (D.obj b.2.1) (Localization.Away ((D.map b.2.2).hom (a b j)))
          (f₀ x).val := congrArg _ (AlgHom.congr_fun hbase x.val).symm
      _ = (fT (f₀ x)).val := (hfT (f₀ x)).symm
  have hbij := awayMap_bijective_of_localizations f₀.toRingHom zS ψ.toRingHom hcomm hψ
  have ha : a b j ∈ qS.range := hzS ▸ zS.property
  refine ⟨ha, ?_⟩
  have hpoint : zS = (⟨a b j, ha⟩ : qS.range) := Subtype.ext hzS
  exact hpoint ▸ hbij

private theorem imageArrow_open {R : Subalgebra ℤ K}
    (models : ∀ n, Subalgebra R (genericAt D L a n))
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
      maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b))
    (b : DiagramArrow C) [Fintype (L b)]
    (ha : ∀ j, a b j ∈ models (.inl b.1))
    (hlocal : ∀ j, Function.Bijective (Localization.awayMap
      (imageMap D L a models maps preserve (.inl b)).toRingHom
      (⟨a b j, ha j⟩ : models (.inl b.1))))
    (hbase : maps (.inl b) = (D.map b.2.2).hom)
    (c : L b → D.obj b.2.1)
    (hc : ∑ j, c j * (D.map b.2.2).hom (a b j) = 1)
    (hcoeff : ∀ j, c j ∈ models (.inl b.2.1)) :
    AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl b)).toRingHom)) := by
  apply isOpenImmersion_of_away_maps
    (imageMap D L a models maps preserve (.inl b)).toRingHom
    (fun j ↦ (⟨a b j, ha j⟩ : models (.inl b.1))) ?_ hlocal
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨fun j ↦ (⟨c j, hcoeff j⟩ : models (.inl b.2.1)), ?_⟩
  apply (show Function.Injective (models (.inl b.2.1)).val from Subtype.val_injective)
  erw [map_sum, map_one]
  change (∑ j, c j * (show D.obj b.2.1 from maps (.inl b) (a b j))) = 1
  erw [hbase]
  exact hc

/-- Coefficient images retain affine open arrows and prescribed finite elements. -/
theorem exists_open_images
    [Finite C] [∀ i j : C, Finite (i ⟶ j)] [∀ b, Finite (L b)]
    [∀ i, Algebra.FinitePresentation S (D₀.obj i)] (hS : S.FG)
    (e : ∀ i, K ⊗[S] D₀.obj i ≃ₐ[K] D.obj i)
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    (hg : ∀ b j, e b.1 ((1 : K) ⊗ₜ[S] g b j) = a b j)
    (hlocal : ∀ b j, Function.Bijective
      (Localization.awayMap (D.map b.2.2).hom.toRingHom (a b j)))
    (hcover : ∀ b, Ideal.span (Set.range (fun j ↦ (D.map b.2.2).hom (a b j))) = ⊤)
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (hbase : ∀ b, maps (.inl b) = (D.map b.2.2).hom)
    (hforward : ∀ b j, maps (.inr (⟨b, j⟩, .inr false)) =
      Localization.awayMapₐ (D.map b.2.2).hom (a b j))
    (hinverse : ∀ b j, (maps (.inr (⟨b, j⟩, .inr false))).comp
      (maps (.inr (⟨b, j⟩, .inr true))) = AlgHom.id K _)
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth S (D₀.obj i))
    (J : PrincipalNode L → Type*) [∀ n, Finite (J n)]
    (elements : ∀ n, J n → genericAt D L a n) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (models : ∀ n, Subalgebra R (genericAt D L a n))
        (comparison : ∀ n, K ⊗[R] models n ≃ₐ[K] genericAt D L a n)
        (preserve : ∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
          maps b (x : genericAt D L a (edgeSrc L b)) ∈ models (edgeTgt L b)),
        R.FG ∧
        (∀ n, models n = (scalarImageHom (R := R)
          (localizationComparisons D₀ D L g a e hnatural hg n)).range) ∧
        (∀ n, Algebra.FinitePresentation R (models n)) ∧
        (∀ i, i ∈ smoothNodes → Algebra.Smooth R (models (.inl i))) ∧
        (∀ n (k : K) (m : models n),
          comparison n (k ⊗ₜ[R] m) =
            algebraMap K (genericAt D L a n) k * (m : genericAt D L a n)) ∧
        (∀ b : DiagramArrow C, AlgebraicGeometry.IsOpenImmersion
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (imageMap D L a models maps preserve (.inl b)).toRingHom))) ∧
        ∀ n j, elements n j ∈ models n := by
  classical
  let (b : DiagramArrow C) : Fintype (L b) := Fintype.ofFinite (L b)
  choose c hc using fun b : DiagramArrow C ↦ Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : D.obj b.2.1) ∈ Ideal.span
      (Set.range (fun j ↦ (D.map b.2.2).hom (a b j))) by rw [hcover b]; trivial)
  obtain ⟨R, hSR, hmodels⟩ := exists_localization_images D₀ D L g a hS e hnatural hg
    maps smoothNodes hsm c J elements
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  obtain ⟨models, comparison, hfgR, hintrinsic, hfpR, hsmoothR,
    heval, preserve, helts, hmore⟩ := hmodels
  have haway (b : DiagramArrow C) (j : L b) :
      ∃ ha : a b j ∈ models (.inl b.1), Function.Bijective (Localization.awayMap
        (imageMap D L a models maps preserve (.inl b)).toRingHom
          (⟨a b j, ha⟩ : models (.inl b.1))) := by
    let E := AlgEquiv.ofBijective
      (Localization.awayMapₐ (D.map b.2.2).hom (a b j)) (hlocal b j)
    have hb : maps (.inr (⟨b, j⟩, .inr true)) = E.symm.toAlgHom := by
      apply AlgHom.ext
      intro x
      apply E.injective
      have h := AlgHom.congr_fun (hinverse b j) x
      change maps (.inr (⟨b, j⟩, .inr false))
        (maps (.inr (⟨b, j⟩, .inr true)) x) = x at h
      exact ((AlgHom.congr_fun (hforward b j)
        (maps (.inr (⟨b, j⟩, .inr true)) x)).symm.trans h).trans
          (E.apply_symm_apply x).symm
    exact imageArrow_away_bijective D₀ D L g a e hnatural hg models hintrinsic
      maps preserve b j (hbase b) (hlocal b j) (hforward b j) hb
  choose ha haway using haway
  refine ⟨R, hSR, models, comparison, preserve, hfgR, hintrinsic,
    hfpR, hsmoothR, heval, ?_, hmore⟩
  intro b
  exact imageArrow_open D L a models maps preserve b (ha b) (haway b) (hbase b)
    (c b) (hc b) (fun j ↦ helts (.inl b.2.1) ⟨b.1, b.2.2, j⟩)


end PrincipalDiagram

end FrobeniusSplitting
