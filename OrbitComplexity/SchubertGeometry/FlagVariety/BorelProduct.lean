import OrbitComplexity.GroupActions.Varieties.AffineMulSmooth
import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionCoordinates
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import OrbitComplexity.GroupActions.Varieties.OppositeBorelPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupOppositeTangent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Smooth multiplication of opposite Borel subgroups

The two Borel tangent images span the group tangent algebra because the opposite
unipotent tangent complements the chosen Borel tangent. Restricted multiplication
is therefore smooth in either order and is universally open. The pair formulas
identify these morphisms on points valued in every scheme over the base field.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open GroupActions ReductiveGroups TauCeti
open scoped TensorProduct CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateSmooth : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
attribute [local instance] coordinateSmooth

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra :=
  TauCeti.isReduced_of_smooth K G.coordinateAlgebra
attribute [local instance] coordinateReduced

omit [CharZero K] in
private theorem borelSmooth : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
private theorem oppositeSmooth : Algebra.Smooth K G.oppositeBorelAlgebra :=
  G.oppositeBorel_smooth
attribute [local instance] borelSmooth oppositeSmooth

private abbrev qB : G.coordinateAlgebra →ₐc[K] G.borelAlgebra :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom
private abbrev qO : G.coordinateAlgebra →ₐc[K] G.oppositeBorelAlgebra :=
  (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.oppositeBorelIdeal).hom

private theorem tangent_sup :
    (derivationCompLieHom (B := K) (qB G)).range.toSubmodule ⊔
      (derivationCompLieHom (B := K) (qO G)).range.toSubmodule = ⊤ := by
  change G.borelTangent.toSubmodule ⊔
    (G.subgroupTangent G.oppositeBorelIdeal).toSubmodule = ⊤
  have hI : G.oppositeBorelIdeal ≤ G.oppositeUnipotentIdeal :=
    HopfIdeal.conjugate_mono G.longestPoint G.borel_le_unipotentIdeal
  have hT : G.oppositeUnipotentTangent.toSubmodule ≤
      (G.subgroupTangent G.oppositeBorelIdeal).toSubmodule :=
    hopfQuotient_tangentImage_antitone _ _ hI
  apply top_unique
  rw [← G.oppositeUnipotent_sup_borel]
  exact sup_le (hT.trans le_sup_right) le_sup_left

omit [CharZero K] in
private theorem restricted_mul_smooth {A B : Type u}
    [CommRing A] [HopfAlgebra K A] [Algebra.Smooth K A]
    [CommRing B] [HopfAlgebra K B] [Algebra.Smooth K B]
    (f : G.coordinateAlgebra →ₐc[K] A) (g : G.coordinateAlgebra →ₐc[K] B)
    (h : (derivationCompLieHom (B := K) f).range.toSubmodule ⊔
      (derivationCompLieHom (B := K) g).range.toSubmodule = ⊤) :
    letI : IsReduced A := TauCeti.isReduced_of_smooth K A
    letI : IsReduced B := TauCeti.isReduced_of_smooth K B
    Smooth (((fst (affineVariety K A).toOver (affineVariety K B).toOver ≫
      affineMorphism f.toAlgHom) *
      (snd (affineVariety K A).toOver (affineVariety K B).toOver ≫
        affineMorphism g.toAlgHom)).left) := by
  let : IsReduced A := TauCeti.isReduced_of_smooth K A
  let : IsReduced B := TauCeti.isReduced_of_smooth K B
  let : Algebra.Smooth K (A ⊗[K] B) := Algebra.Smooth.comp K A _
  let : IsReduced (A ⊗[K] B) := TauCeti.isReduced_of_smooth K (A ⊗[K] B)
  let F := ((fst (affineVariety K A).toOver (affineVariety K B).toOver ≫
    affineMorphism f.toAlgHom) *
      (snd (affineVariety K A).toOver (affineVariety K B).toOver ≫
        affineMorphism g.toAlgHom))
  let e := affineTensorIso K A B
  have he : (e.hom ≫ F).left =
      (affineMorphism (affineMulMap f.toAlgHom g.toAlgHom)).left :=
    congrArg Over.Hom.left (affineTensorIso_mul f.toAlgHom g.toAlgHom)
  have hs : Smooth (affineMorphism (affineMulMap f.toAlgHom g.toAlgHom)).left :=
    HasRingHomProperty.Spec_iff.mpr
      (affineMulMap_smooth f g (affineMulTangent_surjective_of_sup f g h))
  let es := (Over.forget (Spec (CommRingCat.of K))).mapIso e
  have hcomp : Smooth ((e.hom ≫ F).left) := he.symm ▸ hs
  have : Smooth (es.hom ≫ F.left) := hcomp
  have hc : Smooth (es.inv ≫ (es.hom ≫ F.left)) := inferInstance
  change Smooth F.left
  simpa only [Iso.inv_hom_id_assoc] using hc

/-- Multiplication from the chosen Borel and its opposite into the reductive group. -/
def borelOppositeMul : (borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver ⟶
    (reductiveVariety G).toOver :=
  (fst (borelVariety G).toOver (oppositeBorelVariety G).toOver ≫ borelInclusion G) *
    (snd (borelVariety G).toOver (oppositeBorelVariety G).toOver ≫ oppositeBorelInclusion G)

/-- Multiplication from opposite Borel and Borel into the reductive group. -/
def oppositeBorelMul : (oppositeBorelVariety G).toOver ⊗ (borelVariety G).toOver ⟶
    (reductiveVariety G).toOver :=
  (fst (oppositeBorelVariety G).toOver (borelVariety G).toOver ≫ oppositeBorelInclusion G) *
    (snd (oppositeBorelVariety G).toOver (borelVariety G).toOver ≫ borelInclusion G)

/-- Borel times opposite Borel multiplication is smooth. -/
instance borelOppositeMul_smooth : Smooth (borelOppositeMul G).left := by
  exact restricted_mul_smooth G (qB G) (qO G) (tangent_sup G)

/-- Opposite Borel times Borel multiplication is smooth. -/
instance oppositeBorelMul_smooth : Smooth (oppositeBorelMul G).left := by
  apply restricted_mul_smooth G (qO G) (qB G)
  rw [sup_comm]
  exact tangent_sup G

/-- Borel and opposite-Borel scheme-valued points multiply by their ambient inclusions. -/
theorem borelOppositeMul_pair {S : Over (Spec (CommRingCat.of K))}
    (b : S ⟶ (borelVariety G).toOver) (o : S ⟶ (oppositeBorelVariety G).toOver) :
    lift b o ≫ borelOppositeMul G =
      (b ≫ borelInclusion G) * (o ≫ oppositeBorelInclusion G) := by
  rw [borelOppositeMul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

/-- Opposite-Borel and Borel scheme-valued points multiply by their ambient inclusions. -/
theorem oppositeBorelMul_pair {S : Over (Spec (CommRingCat.of K))}
    (o : S ⟶ (oppositeBorelVariety G).toOver) (b : S ⟶ (borelVariety G).toOver) :
    lift o b ≫ oppositeBorelMul G =
      (o ≫ oppositeBorelInclusion G) * (b ≫ borelInclusion G) := by
  rw [oppositeBorelMul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

end
end SchubertGeometry
