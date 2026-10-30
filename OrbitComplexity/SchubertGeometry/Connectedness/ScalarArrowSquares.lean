import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention

/-! # Scalar morphisms and their original projections

An isomorphism to a scalar pullback is determined by its two projections.
The resulting naturality equation uses the given objects and isomorphisms
directly. Iterated scalar morphisms retain their original projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry

universe u

/-- Projection equations determine the naturality square of two scalar
comparison isomorphisms over an arbitrary base scheme. -/
theorem scalarArrow_square {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} {A D : Over T}
    (E : A ≅ Over.mk (pullback.fst κ X.hom))
    (F : D ≅ Over.mk (pullback.fst κ Y.hom))
    (f : X ⟶ Y) (a : A ⟶ D)
    (πA : A.left ⟶ X.left) (πD : D.left ⟶ Y.left)
    (hE : E.hom.left ≫ pullback.snd κ X.hom = πA)
    (hF : F.hom.left ≫ pullback.snd κ Y.hom = πD)
    (h : πA ≫ f.left = a.left ≫ πD) :
    E.hom ≫ chosenScalarArrow κ f = a ≫ F.hom := by
  let c : A ⟶ Over.mk (pullback.fst κ Y.hom) :=
    E.hom ≫ chosenScalarArrow κ f
  let d : A ⟶ Over.mk (pullback.fst κ Y.hom) := a ≫ F.hom
  change c = d
  apply CostructuredArrow.hom_ext
  apply pullback.hom_ext
  · exact c.w.trans d.w.symm
  · change (E.hom.left ≫ (chosenScalarArrow κ f).left) ≫
        pullback.snd κ Y.hom =
      (a.left ≫ F.hom.left) ≫ pullback.snd κ Y.hom
    calc
      _ = πA ≫ f.left := by
        rw [Category.assoc, chosenScalarArrow_snd, ← Category.assoc, hE]
      _ = a.left ≫ πD := h
      _ = _ := by rw [Category.assoc, hF]

/-- The morphism obtained by two scalar extensions commutes with the
composite projection to the original model. -/
theorem doubleScalarArrow_snd {B T U : Scheme.{u}}
    (κ : T ⟶ B) (τ : U ⟶ T) {X Y : Over B} (f : X ⟶ Y) :
    (chosenScalarArrow τ (chosenScalarArrow κ f)).left ≫
        pullback.snd τ (pullback.fst κ Y.hom) ≫ pullback.snd κ Y.hom =
      pullback.snd τ (pullback.fst κ X.hom) ≫
        pullback.snd κ X.hom ≫ f.left := by
  have hτ := chosenScalarArrow_snd τ (chosenScalarArrow κ f)
  change (chosenScalarArrow τ (chosenScalarArrow κ f)).left ≫
      pullback.snd τ (pullback.fst κ Y.hom) =
    pullback.snd τ (pullback.fst κ X.hom) ≫ (chosenScalarArrow κ f).left at hτ
  rw [← Category.assoc, hτ, Category.assoc, chosenScalarArrow_snd]

/-- The fibre over a specified section, regarded as an object over the base. -/
def fibreModel {B : Scheme.{u}} {F Q : Over B}
    (π : F ⟶ Q) (b : Over.mk (𝟙 B) ⟶ Q) : Over B :=
  Over.mk (pullback.snd π.left b.left)

/-- The canonical inclusion of the fibre over a section. -/
def fibreProjection {B : Scheme.{u}} {F Q : Over B}
    (π : F ⟶ Q) (b : Over.mk (𝟙 B) ⟶ Q) : fibreModel π b ⟶ F :=
  Over.homMk (pullback.fst π.left b.left) (by
    calc
      pullback.fst π.left b.left ≫ F.hom =
          pullback.fst π.left b.left ≫ (π.left ≫ Q.hom) :=
        congrArg (fun f => pullback.fst π.left b.left ≫ f) π.w.symm
      _ = (pullback.fst π.left b.left ≫ π.left) ≫ Q.hom :=
        (Category.assoc _ _ _).symm
      _ = (pullback.snd π.left b.left ≫ b.left) ≫ Q.hom :=
        congrArg (fun f => f ≫ Q.hom) (pullback.condition (f := π.left) (g := b.left))
      _ = pullback.snd π.left b.left := by
        rw [Category.assoc, b.w]
        change pullback.snd π.left b.left ≫ 𝟙 B = pullback.snd π.left b.left
        exact Category.comp_id _)

/-- The section obtained by scalar extension of a given section. -/
def scalarSection {T : Type*} [Category T] [HasPullbacks T]
    {B A Q : T} (κ : A ⟶ B) (q : Q ⟶ B) (b : B ⟶ Q) (hb : b ≫ q = 𝟙 B) :
    A ⟶ pullback κ q :=
  pullback.lift (𝟙 A) (κ ≫ b) (by simp only [Category.id_comp, Category.assoc, hb,
    Category.comp_id])

/-- A scalar-extended morphism forms a Cartesian square with its projections. -/
theorem scalarArrow_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    IsPullback (chosenScalarArrow κ f).left (pullback.snd κ X.hom)
      (pullback.snd κ Y.hom) f.left := by
  have hf : (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom := by
    have hw := (chosenScalarArrow κ f).w
    change (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom at hw
    exact hw
  have h : IsPullback ((chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom)
      (pullback.snd κ X.hom) κ (f.left ≫ Y.hom) := by
    rw [hf, f.w]
    exact IsPullback.of_hasPullback κ X.hom
  exact h.of_right (chosenScalarArrow_snd κ f) (IsPullback.of_hasPullback κ Y.hom)

/-- The lift into the scalar extension of a fibre satisfies its section triangle. -/
theorem scalarFibre_lift_triangle {T : Type*} [Category T]
    {X Fj Qj F Q B A : T}
    (d : X ⟶ Fj) (πj : Fj ⟶ Qj) (a : X ⟶ A) (s : A ⟶ Qj)
    (pF : Fj ⟶ F) (pQ : Qj ⟶ Q) (q : Qj ⟶ A)
    (π : F ⟶ Q) (κ : A ⟶ B) (b : B ⟶ Q) (q₀ : Q ⟶ B)
    (hQ : IsPullback pQ q q₀ κ)
    (hπ : πj ≫ pQ = pF ≫ π) (hd : (d ≫ pF) ≫ π = a ≫ (κ ≫ b))
    (hs : s ≫ pQ = κ ≫ b) (hbase : (d ≫ πj) ≫ q = a)
    (hsec : s ≫ q = 𝟙 A) : d ≫ πj = a ≫ s := by
  apply hQ.hom_ext
  · calc
      (d ≫ πj) ≫ pQ = d ≫ (pF ≫ π) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => d ≫ k) hπ)
      _ = (d ≫ pF) ≫ π := (Category.assoc _ _ _).symm
      _ = a ≫ (κ ≫ b) := hd
      _ = (a ≫ s) ≫ pQ :=
        (congrArg (fun k => a ≫ k) hs.symm).trans (Category.assoc _ _ _).symm
  · exact hbase.trans
      ((Category.assoc a s q).trans
        ((congrArg (fun k => a ≫ k) hsec).trans (Category.comp_id a))).symm

/-- Formation of a fibre over a section commutes with scalar extension. -/
theorem scalarFibre_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {F Q : Over B} (π : F ⟶ Q) (b : Over.mk (𝟙 B) ⟶ Q) :
    IsPullback (chosenScalarArrow κ (fibreProjection π b)).left
      (pullback.fst κ (fibreModel π b).hom)
      (chosenScalarArrow κ π).left (scalarSection κ Q.hom b.left b.w) := by
  let W := fibreModel π b
  let p := fibreProjection π b
  let d := (chosenScalarArrow κ p).left
  let a := pullback.fst κ W.hom
  let s := scalarSection κ Q.hom b.left b.w
  have hd : (d ≫ pullback.snd κ F.hom) ≫ π.left = a ≫ (κ ≫ b.left) := by
    calc
      (d ≫ pullback.snd κ F.hom) ≫ π.left =
          (pullback.snd κ W.hom ≫ pullback.fst π.left b.left) ≫ π.left :=
        congrArg (fun k => k ≫ π.left) (chosenScalarArrow_snd κ p)
      _ = pullback.snd κ W.hom ≫ (pullback.snd π.left b.left ≫ b.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => pullback.snd κ W.hom ≫ k)
            (pullback.condition (f := π.left) (g := b.left)))
      _ = (pullback.snd κ W.hom ≫ W.hom) ≫ b.left := (Category.assoc _ _ _).symm
      _ = (a ≫ κ) ≫ b.left :=
        congrArg (fun k => k ≫ b.left)
          (pullback.condition (f := κ) (g := W.hom)).symm
      _ = a ≫ (κ ≫ b.left) := Category.assoc _ _ _
  have hc : d ≫ (chosenScalarArrow κ π).left = a ≫ s :=
    scalarFibre_lift_triangle d (chosenScalarArrow κ π).left a s
      (pullback.snd κ F.hom) (pullback.snd κ Q.hom) (pullback.fst κ Q.hom)
      π.left κ b.left Q.hom (IsPullback.of_hasPullback κ Q.hom).flip
      (chosenScalarArrow_snd κ π) hd (pullback.lift_snd _ _ _)
      (chosenScalarArrow κ p ≫ chosenScalarArrow κ π).w (pullback.lift_fst _ _ _)
  have hout : IsPullback (d ≫ pullback.snd κ F.hom) a π.left
      (s ≫ pullback.snd κ Q.hom) := by
    rw [chosenScalarArrow_snd κ p, show s ≫ pullback.snd κ Q.hom = κ ≫ b.left from
      pullback.lift_snd _ _ _]
    exact (IsPullback.of_hasPullback κ W.hom).flip.paste_horiz
      (IsPullback.of_hasPullback π.left b.left)
  exact hout.of_right hc (scalarArrow_cartesian κ π).flip

/-- The comparison between two isomorphisms retains their common source. -/
theorem scalarComparison_iso_triangle {T : Type*} [Category T]
    {X A B : T} (E : X ≅ A) (F : X ≅ B) :
    E.hom ≫ (E.symm ≪≫ F).hom = F.hom := by
  exact E.hom_inv_id_assoc F.hom

/-- Compatible coefficient and target comparisons retain a curve triangle. -/
theorem scalarCurve_comparison_triangle {T : Type*} [Category T]
    {X G H P W R : T} (qG : X ⟶ G) (qH : X ⟶ H) (eG : G ⟶ H)
    (cG : G ⟶ P) (cH : H ⟶ W) (eP : P ⟶ W) (hR : R ⟶ P)
    (qR : X ⟶ R) (eR : R ⟶ W) (qW : X ⟶ W)
    (hcommon : qG ≫ eG = qH) (hstage : cG ≫ eP = eG ≫ cH)
    (hcoeff : qR ≫ hR = qG ≫ cG) (hiso : hR ≫ eP = eR)
    (hqW : qH ≫ cH = qW) : qW = qR ≫ eR := by
  symm
  calc
    qR ≫ eR = qR ≫ (hR ≫ eP) := congrArg (fun k => qR ≫ k) hiso.symm
    _ = (qR ≫ hR) ≫ eP := (Category.assoc _ _ _).symm
    _ = (qG ≫ cG) ≫ eP := congrArg (fun k => k ≫ eP) hcoeff
    _ = qG ≫ (eG ≫ cH) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => qG ≫ k) hstage)
    _ = (qG ≫ eG) ≫ cH := (Category.assoc _ _ _).symm
    _ = qH ≫ cH := congrArg (fun k => k ≫ cH) hcommon
    _ = qW := hqW


/-- Commuting squares remain commuting after composition of their horizontal maps. -/
theorem scalarArrow_composite_square {T : Type*} [Category T]
    {A B C A' B' C' : T} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A' ⟶ B') (g' : B' ⟶ C') (a : A ⟶ A')
    (b : B ⟶ B') (c : C ⟶ C')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') :
    (f ≫ g) ≫ c = a ≫ (f' ≫ g') := by
  calc
    (f ≫ g) ≫ c = f ≫ (g ≫ c) := Category.assoc _ _ _
    _ = f ≫ (b ≫ g') := congrArg (fun k => f ≫ k) hg
    _ = (f ≫ b) ≫ g' := (Category.assoc _ _ _).symm
    _ = (a ≫ f') ≫ g' := congrArg (fun k => k ≫ g') hf
    _ = a ≫ (f' ≫ g') := Category.assoc _ _ _


end SchubertGeometry
