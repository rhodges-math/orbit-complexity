import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineScalarCoordinates
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.GraphEndpoint
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.EndpointProducts
import Mathlib.RingTheory.TensorProduct.Pi
import Batteries.Tactic.OpenPrivate

/-! # Coordinate comparison on the chosen endpoint cover

An affine cover of the specified model source is pulled back along its original
scalar comparison. The original endpoint square then determines the coordinate
map on every one of these charts. Its product is the original cover-section
map, rather than a separately chosen map with the same point image.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open FrobeniusSplitting

namespace SchubertGeometry

noncomputable section

universe u

open private square_of_pure_one
  from OrbitComplexity.SchubertGeometry.Normality.Coordinates.EndpointProducts

/-- Scalar Cartesian comparisons of the specified endpoint construct the
tensor-coordinate comparisons on the exact pulled-back source cover. The
product square identifies the scalar extension of the model cover-section
map with the original generic cover-section map. -/
theorem exists_chosen_cover_coordinates {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀]
    (x₀ : X₀ ⟶ Spec (.of R)) (y₀ : Y₀ ⟶ Spec (.of R))
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hfK : f ≫ y = x)
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hf : f ≫ qY = qX ≫ f₀)
    (V : X₀.OpenCover.{u}) [Finite V.I₀]
    (hV : ∀ j, IsAffine (V.X j)) :
    let VK := V.pullback₂ qX
    let fR : Over.mk x₀ ⟶ Over.mk y₀ := Over.homMk f₀ hf₀
    let fK : Over.mk x ⟶ Over.mk y := Over.homMk f hfK
    let M₀ : Type u := ((algΓ (.of R)).obj (Over.mk y₀)).unop
    let M : Type u := ((algΓ (.of K)).obj (Over.mk y)).unop
    let N₀ (j : V.I₀) : Type u :=
      ((algΓ (.of R)).obj (Over.mk (V.f j ≫ x₀))).unop
    let N (j : V.I₀) : Type u :=
      ((algΓ (.of K)).obj (Over.mk (VK.f j ≫ x))).unop
    let := Fintype.ofFinite V.I₀
    let := Classical.decEq V.I₀
    ∃ (eM : K ⊗[R] M₀ ≃ₐ[K] M)
      (eN : ∀ j, K ⊗[R] N₀ j ≃ₐ[K] N j),
      (∀ a, eM ((1 : K) ⊗ₜ[R] a) = qY.appTop.hom a) ∧
      (∀ j a, eN j ((1 : K) ⊗ₜ[R] a) =
        (pullback.fst (V.f j) qX).appTop.hom a) ∧
      ((Algebra.TensorProduct.piRight R K K N₀).trans
        (AlgEquiv.piCongrRight eN)).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (affineCoverSectionMap fR V)) =
            (affineCoverSectionMap fK VK).comp eM.toAlgHom := by
  classical
  let VK := V.pullback₂ qX
  let M₀ : Type u := ((algΓ (.of R)).obj (Over.mk y₀)).unop
  let M : Type u := ((algΓ (.of K)).obj (Over.mk y)).unop
  let N₀ (j : V.I₀) : Type u :=
    ((algΓ (.of R)).obj (Over.mk (V.f j ≫ x₀))).unop
  let N (j : V.I₀) : Type u :=
    ((algΓ (.of K)).obj (Over.mk (VK.f j ≫ x))).unop
  let : Algebra R M₀ :=
    (((algΓ (.of R)).obj (Over.mk y₀)).unop).algebra
  let : Algebra K M :=
    (((algΓ (.of K)).obj (Over.mk y)).unop).algebra
  let (j : V.I₀) : Algebra R (N₀ j) :=
    (((algΓ (.of R)).obj (Over.mk (V.f j ≫ x₀))).unop).algebra
  let (j : V.I₀) : Algebra K (N j) :=
    (((algΓ (.of K)).obj (Over.mk (VK.f j ≫ x))).unop).algebra
  let : Algebra R Γ(Y₀, ⊤) :=
    (y₀.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(Y, ⊤) :=
    (y.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let (j : V.I₀) : Algebra R Γ(V.X j, ⊤) :=
    ((V.f j ≫ x₀).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let (j : V.I₀) : Algebra K Γ(VK.X j, ⊤) :=
    ((VK.f j ≫ x).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let := Fintype.ofFinite V.I₀
  obtain ⟨eM, _, heM, _⟩ :=
    exists_affine_scalar_coordinates y₀ y qY hY
  have coordinates (j : V.I₀) :
      ∃ e : K ⊗[R] N₀ j ≃ₐ[K] N j,
        ∀ a, e ((1 : K) ⊗ₜ[R] a) =
          (pullback.fst (V.f j) qX).appTop.hom a := by
    let : IsAffine (V.X j) := hV j
    have hchart : IsPullback (pullback.fst (V.f j) qX)
        (VK.f j ≫ x) (V.f j ≫ x₀)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
      (IsPullback.of_hasPullback (V.f j) qX).paste_vert hX
    obtain ⟨e, _, he, _⟩ := exists_affine_scalar_coordinates
      (V.f j ≫ x₀) (VK.f j ≫ x) (pullback.fst (V.f j) qX) hchart
    exact ⟨e, he⟩
  choose eN heN using coordinates
  have hchart (j : V.I₀) :
      (VK.f j ≫ f) ≫ qY =
        pullback.fst (V.f j) qX ≫ (V.f j ≫ f₀) := by
    change (pullback.snd (V.f j) qX ≫ f) ≫ qY = _
    rw [Category.assoc, hf, ← Category.assoc, ← pullback.condition,
      Category.assoc]
  refine ⟨eM, eN, heM, heN, ?_⟩
  apply square_of_pure_one (M := M₀) (N := ∀ j, N₀ j)
    (A := M) (B := ∀ j, N j)
  intro a
  apply funext
  intro j
  let φ₀ : M₀ →ₐ[R] N₀ j := ((algΓ (.of R)).map
    (Over.homMk (V.f j ≫ f₀) (by
      change (V.f j ≫ f₀) ≫ y₀ = V.f j ≫ x₀
      rw [Category.assoc, hf₀]) :
        Over.mk (V.f j ≫ x₀) ⟶ Over.mk y₀)).unop.hom
  let φ : M →ₐ[K] N j := ((algΓ (.of K)).map
    (Over.homMk (VK.f j ≫ f) (by
      change (VK.f j ≫ f) ≫ y = VK.f j ≫ x
      rw [Category.assoc, hfK]) :
        Over.mk (VK.f j ≫ x) ⟶ Over.mk y)).unop.hom
  change eN j ((1 : K) ⊗ₜ[R] φ₀ (a : M₀)) =
    φ (eM ((1 : K) ⊗ₜ[R] (a : M₀)))
  have ha := congrArg
    (fun g : (VK.X j) ⟶ Y₀ ↦ g.appTop.hom a) (hchart j)
  exact (heN j (φ₀ a)).trans (ha.symm.trans (congrArg φ (heM a).symm))

/-- Pulling sections back to an open cover through a quasi-compact surjection
onto a reduced scheme is injective. -/
theorem coverSectionMap_injective {K : Type u} [CommRing K]
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f : X ⟶ Y) (hf : f ≫ y = x) (V : X.OpenCover)
    [QuasiCompact f] [Surjective f] [IsReduced Y] :
    Function.Injective (affineCoverSectionMap
      (Over.homMk f hf : Over.mk x ⟶ Over.mk y) V) := by
  let : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  intro a b h
  apply f.app_injective ⊤
  apply V.ext_elem
  intro j
  exact congrFun h j

/-- The original chosen model cover-section map is generically injective.
Its tensor comparison is constructed from the chosen scalar Cartesian squares
and the original endpoint equation; no comparison with an independently
selected source cover is required. -/
theorem chosen_cover_tensor_injective {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    {X₀ Y₀ X Y : Scheme.{u}} [IsAffine Y₀]
    (x₀ : X₀ ⟶ Spec (.of R)) (y₀ : Y₀ ⟶ Spec (.of R))
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hfK : f ≫ y = x)
    [QuasiCompact f] [Surjective f] [IsReduced Y]
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hf : f ≫ qY = qX ≫ f₀)
    (V : X₀.OpenCover.{u}) [Finite V.I₀]
    (hV : ∀ j, IsAffine (V.X j)) :
    Function.Injective (Algebra.TensorProduct.lTensor (S := K) K
      (affineCoverSectionMap
        (Over.homMk f₀ hf₀ : Over.mk x₀ ⟶ Over.mk y₀) V)) := by
  classical
  let := Fintype.ofFinite V.I₀
  let VK := V.pullback₂ qX
  obtain ⟨eM, eN, _, _, hsquare⟩ :=
    exists_chosen_cover_coordinates x₀ y₀ x y f₀ f hf₀ hfK qX qY hX hY hf V hV
  intro a b hab
  apply eM.injective
  apply coverSectionMap_injective x y f hfK VK
  have ha := AlgHom.congr_fun hsquare a
  have hb := AlgHom.congr_fun hsquare b
  exact ha.symm.trans ((congrArg
    (((Algebra.TensorProduct.piRight R K K
      (fun j : V.I₀ ↦ (((algΓ (.of R)).obj (Over.mk (V.f j ≫ x₀))).unop : Type u))).trans
        (AlgEquiv.piCongrRight eN)).toAlgHom) hab).trans hb)

end
end SchubertGeometry
