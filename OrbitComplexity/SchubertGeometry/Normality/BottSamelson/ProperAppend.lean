import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ProperAppendAssembly
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.BsdhModelBase

/-! # append models retaining the specified proper prior model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

/-- The endpoint charts construct the next model over the specified
proper prior model, retaining its coefficient square and original projection. -/
theorem exists_proper_append {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (qY : bsdhScheme G word ⟶ Y)
    (hY : IsPullback qY (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (U : Y.OpenCover.{u}) [Finite U.I₀] (hU : ∀ j, IsAffine (U.X j)) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      R.FG ∧ ∃ (Y₀ Z : Scheme.{u}) (base₀ : Y₀ ⟶ Spec (.of R))
        (baseZ : Z ⟶ Spec (.of R)) (q₀ : Y₀ ⟶ Y) (q : Z ⟶ Y₀)
        (m₀ : bsdhScheme G word ⟶ Y₀)
        (m : bsdhScheme G (word ++ [i]) ⟶ Z),
        IsProper base₀ ∧ Smooth base₀ ∧
        IsPullback q₀ base₀ base (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
        IsPullback m₀ (bsdhToSpec G word) base₀
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        m₀ ≫ q₀ = qY ∧ baseZ = q ≫ base₀ ∧
        IsProper baseZ ∧ Smooth baseZ ∧
        IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
        IsPullback m (bsdhAppendFst G word i) q m₀ ∧
        IsPullback m (bsdhToSpec G (word ++ [i])) baseZ
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        ∃ (δ : Y₀ ⟶ Z) (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i])),
          δ ≫ q = 𝟙 _ ∧ IsClosedImmersion δ ∧ δ ≫ baseZ = base₀ ∧
          IsClosedImmersion d ∧ d ≫ bsdhAppendFst G word i = 𝟙 _ ∧
          d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word ∧ d ≫ m = m₀ ≫ δ := by
  classical
  obtain ⟨V, _hVfinite, _hVaffine, g, a, ha, Hc⟩ :=
    bsdh_finite_endpoint_cover G word i
  choose c hcart _hopen hend using Hc
  obtain ⟨T, hST, HT⟩ := exists_proper_endpoint_charts G word i S hS base qY hY
    U hU V g a ha c hcart hend
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  obtain ⟨hT, YT, baseT, qT, mT, hproperT, hsmoothT, hTcart, hKcart, hmq,
    W, hWfinite, hWaffine, endpoint, _hcover, _hWnative, d, _hd, ha', hcart', hend'⟩ := HT
  let : IsProper baseT := hproperT
  let : Smooth baseT := hsmoothT
  let : Finite W.I₀ := hWfinite
  obtain ⟨R, hTR, HR⟩ := exists_proper_append_model G word i T hT baseT mT hKcart
    W hWaffine (fun j ↦ g (endpoint j)) (fun j ↦ d j ≫ a (endpoint j))
    (fun j ↦ (d j ⊗ₘ 𝟙 _) ≫ c (endpoint j)) ha' hcart' hend'
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let hSR : S ≤ R := hST.trans hTR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  obtain ⟨hR, Y₀, Z, base₀, baseZ, qR, q, m₀, m, hproper₀, hsmooth₀, hRcart,
    hm₀, hmprior, hbaseZ, hproperZ, hsmoothZ, hproperq, hsmoothq, hgcq, hmqcart,
    hm, hboundary⟩ := HR
  have hcoeff : Spec.map (CommRingCat.ofHom (algebraMap T R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
      Spec.map (CommRingCat.ofHom (algebraMap S R)) := by
    rw [← Spec.map_comp]
    rfl
  have hprior : IsPullback (qR ≫ qT) base₀ base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) := by
    exact hcoeff ▸ hRcart.paste_horiz hTcart
  have hprojection : m₀ ≫ (qR ≫ qT) = qY := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ qT) hmprior).trans hmq)
  exact ⟨R, hSR, hR, Y₀, Z, base₀, baseZ, qR ≫ qT, q, m₀, m,
    hproper₀, hsmooth₀, hprior, hm₀, hprojection, hbaseZ, hproperZ, hsmoothZ,
    hproperq, hsmoothq, hgcq, hmqcart, hm, hboundary⟩

/-- Every word has a proper smooth arithmetic model with geometrically
connected fibres over an enlargement
of the prescribed coefficient ring, constructed by append models. -/
theorem exists_proper_bsdh_model {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ (R : Subalgebra ℤ K), S ≤ R ∧ R.FG ∧
      ∃ (Y : Scheme.{u}) (base : Y ⟶ Spec (.of R))
        (m : bsdhScheme G word ⟶ Y),
        IsProper base ∧ Smooth base ∧ GeometricallyConnected base ∧
        IsPullback m (bsdhToSpec G word) base
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  classical
  induction word using List.reverseRecOn with
  | nil =>
      obtain ⟨Y, base, m, hproper, hsmooth, hgc, hm⟩ := bsdh_empty_model (S := S) G
      exact ⟨S, le_rfl, hS, Y, base, m, hproper, hsmooth, hgc, hm⟩
  | append_singleton word i ih =>
      obtain ⟨T, hST, hT, YT, baseT, mT, hproperT, hsmoothT, hgcT, hmT⟩ := ih
      let : IsProper baseT := hproperT
      let : Smooth baseT := hsmoothT
      let : CompactSpace YT := QuasiCompact.compactSpace_of_compactSpace baseT
      let U := YT.affineCover.finiteSubcover
      have hU (j : U.I₀) : IsAffine (U.X j) := by
        change IsAffine (YT.affineCover.X (YT.affineCover.idx j.val))
        infer_instance
      obtain ⟨R, hTR, HR⟩ := SchubertGeometry.exists_proper_append G word i T hT baseT mT hmT U hU
      let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
      obtain ⟨hR, Y₀, Z, base₀, baseZ, q₀, q, m₀, m, hproper₀, hsmooth₀, hprior,
        hm₀, hprojection, hbaseZ, hproperZ, hsmoothZ, hproperq, hsmoothq, hgcq,
        hmqcart, hm, _hboundary⟩ := HR
      let : GeometricallyConnected base₀ :=
        MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprior hgcT
      let : GeometricallyConnected q := hgcq
      let : Smooth base₀ := hsmooth₀
      let : Smooth q := hsmoothq
      have hgcZ : GeometricallyConnected baseZ := by
        rw [hbaseZ]
        exact GeometricallyConnected.comp q base₀
      exact ⟨R, hST.trans hTR, hR, Z, baseZ, m, hproperZ, hsmoothZ, hgcZ, hm⟩

end SchubertGeometry
