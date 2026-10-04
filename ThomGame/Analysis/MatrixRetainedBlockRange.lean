module

public import ThomGame.Analysis.MatrixSubalgebraStarBlocks
public import Mathlib.Algebra.Algebra.Pi

/-!
# Positive retained blocks of a concrete matrix range

A matrix representation whose exact kernel consists of discarded factors
gives a star equivalence of its actual range with the retained factors.
The factors are numbered only after taking this restriction.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {n m : Nat} (p : Fin n → Nat) (keep : Fin n → Prop) [DecidablePred keep]
    (φ : ((i : Fin n) → CMatrix (p i)) →⋆ₐ[ℂ] CMatrix m)

noncomputable def matrixRetainedBlockCoordinates (X : φ.range) :
    (i : {i : Fin n // keep i}) → CMatrix (p i.val) :=
  fun i => (Classical.choose X.property) i.val

variable (hφ : ∀ X Y, φ X = φ Y ↔ ∀ i, keep i → X i = Y i)

omit [DecidablePred keep] in
include hφ in
theorem matrixRetainedBlockCoordinates_map (X : (i : Fin n) → CMatrix (p i))
    (i : {i : Fin n // keep i}) :
    matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) i = X i.val := by
  exact (hφ _ X).mp (Classical.choose_spec (show φ X ∈ φ.range from ⟨X, rfl⟩)) i.val i.property

noncomputable def matrixRetainedBlockCoordinatesHom :
    φ.range →⋆ₐ[ℂ] ((i : {i : Fin n // keep i}) → CMatrix (p i.val)) where
  toFun := matrixRetainedBlockCoordinates p keep φ
  map_zero' := by
    funext i
    simpa only [map_zero, Pi.zero_apply] using matrixRetainedBlockCoordinates_map p keep φ hφ 0 i
  map_one' := by
    funext i
    simpa only [map_one, Pi.one_apply] using matrixRetainedBlockCoordinates_map p keep φ hφ 1 i
  map_add' := by
    rintro ⟨_, X, rfl⟩ ⟨_, Y, rfl⟩
    funext i
    change matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X + φ.rangeRestrict Y) i =
      matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) i +
      matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict Y) i
    rw [← map_add φ.rangeRestrict]
    simp only [matrixRetainedBlockCoordinates_map p keep φ hφ, Pi.add_apply]
  map_mul' := by
    rintro ⟨_, X, rfl⟩ ⟨_, Y, rfl⟩
    funext i
    change matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X * φ.rangeRestrict Y) i =
      matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) i *
      matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict Y) i
    rw [← map_mul φ.rangeRestrict]
    simp only [matrixRetainedBlockCoordinates_map p keep φ hφ, Pi.mul_apply]
  commutes' := by
    intro c
    funext i
    simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, Pi.smul_apply, Pi.one_apply] using
      matrixRetainedBlockCoordinates_map p keep φ hφ (algebraMap ℂ _ c) i
  map_star' := by
    rintro ⟨_, X, rfl⟩
    funext i
    change matrixRetainedBlockCoordinates p keep φ (star (φ.rangeRestrict X)) i =
      star (matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) i)
    rw [← map_star φ.rangeRestrict]
    simp only [matrixRetainedBlockCoordinates_map p keep φ hφ, Pi.star_apply]

theorem matrixRetainedBlockCoordinatesHom_bijective :
    Function.Bijective (matrixRetainedBlockCoordinatesHom p keep φ hφ) := by
  constructor
  · rintro ⟨_, X, rfl⟩ ⟨_, Y, rfl⟩ h
    apply Subtype.ext
    apply (hφ X Y).mpr
    intro i hi
    have he := congrFun h ⟨i, hi⟩
    change matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) ⟨i, hi⟩ =
      matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict Y) ⟨i, hi⟩ at he
    simpa only [matrixRetainedBlockCoordinates_map p keep φ hφ] using he
  · intro Y
    let X : (i : Fin n) → CMatrix (p i) := fun i => if hi : keep i then Y ⟨i, hi⟩ else 0
    refine ⟨⟨φ X, ⟨X, rfl⟩⟩, ?_⟩
    funext i
    change matrixRetainedBlockCoordinates p keep φ (φ.rangeRestrict X) i = Y i
    rw [matrixRetainedBlockCoordinates_map p keep φ hφ]
    simp only [X, dite_eq_left i.property]

noncomputable def matrixRetainedBlockRangeEquiv :
    φ.range ≃⋆ₐ[ℂ] ((i : {i : Fin n // keep i}) → CMatrix (p i.val)) :=
  StarAlgEquiv.ofBijective (matrixRetainedBlockCoordinatesHom p keep φ hφ)
    (matrixRetainedBlockCoordinatesHom_bijective p keep φ hφ)

theorem matrixRetainedBlockRangeEquiv_map (X : (i : Fin n) → CMatrix (p i))
    (i : {i : Fin n // keep i}) :
    matrixRetainedBlockRangeEquiv p keep φ hφ (φ.rangeRestrict X) i = X i.val :=
  matrixRetainedBlockCoordinates_map p keep φ hφ X i

noncomputable def matrixRetainedBlockLabelEquiv :
    {i : Fin n // keep i} ≃ Fin (Fintype.card {i : Fin n // keep i}) :=
  Fintype.equivFin _

noncomputable abbrev matrixRetainedBlockLabel
    (i : Fin (Fintype.card {i : Fin n // keep i})) : Fin n :=
  ((matrixRetainedBlockLabelEquiv keep).symm i).val

theorem matrixRetainedBlockLabel_injective : Function.Injective (matrixRetainedBlockLabel keep) :=
  Subtype.val_injective.comp (matrixRetainedBlockLabelEquiv keep).symm.injective

theorem matrixRetainedBlockLabel_mem (i : Fin (Fintype.card {i : Fin n // keep i})) :
    keep (matrixRetainedBlockLabel keep i) :=
  ((matrixRetainedBlockLabelEquiv keep).symm i).property

noncomputable def matrixRetainedBlockFinEquiv :
    ((i : {i : Fin n // keep i}) → CMatrix (p i.val)) ≃⋆ₐ[ℂ]
      ((i : Fin (Fintype.card {i : Fin n // keep i})) →
        CMatrix (p ((matrixRetainedBlockLabelEquiv keep).symm i).val)) :=
  StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.piCongrLeft' ℂ (fun i : {i : Fin n // keep i} => CMatrix (p i.val))
      (matrixRetainedBlockLabelEquiv keep)) (fun _ => rfl)

noncomputable abbrev matrixRetainedBlockRangeBlocks (hp : ∀ i, keep i → 0 < p i) :
    MatrixSubalgebraStarBlocks φ.range where
  count := Fintype.card {i : Fin n // keep i}
  size i := p ((matrixRetainedBlockLabelEquiv keep).symm i).val
  size_pos i := hp _ ((matrixRetainedBlockLabelEquiv keep).symm i).property
  equiv := (matrixRetainedBlockRangeEquiv p keep φ hφ).trans (matrixRetainedBlockFinEquiv p keep)

theorem matrixRetainedBlockRangeBlocks_equiv_map (hp : ∀ i, keep i → 0 < p i)
    (X : (i : Fin n) → CMatrix (p i)) (i : Fin (Fintype.card {i : Fin n // keep i})) :
    (matrixRetainedBlockRangeBlocks p keep φ hφ hp).equiv (φ.rangeRestrict X) i =
      X ((matrixRetainedBlockLabelEquiv keep).symm i).val :=
  matrixRetainedBlockRangeEquiv_map p keep φ hφ X _

end ThomGame.Analysis
