module

public import ThomGame.Analysis.BoundedMatrixSequences
public import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# The supremum operator norm product of the matrix algebras

This is the actual bounded dependent product with the Euclidean matrix
operator norms. Its underlying star algebra is isomorphic to the
previously constructed algebra of uniformly bounded matrix sequences.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped ENNReal Matrix.Norms.L2Operator

variable {ι : Type*}

def MatrixOperatorProduct (dims : ι → Nat) (_hd : ∀ i, 0 < dims i) : Type _ :=
  lp (fun i => CMatrix (dims i)) ∞

variable (dims : ι → Nat) (hd : ∀ i, 0 < dims i)

noncomputable instance matrixOperatorProductCStarAlgebra : CStarAlgebra (MatrixOperatorProduct dims hd) := by
  let : ∀ i, NeZero (dims i) := fun i => ⟨Nat.ne_of_gt (hd i)⟩
  let : CStarAlgebra (lp (fun i => CMatrix (dims i)) ∞) := {}
  exact inferInstanceAs (CStarAlgebra (lp (fun i => CMatrix (dims i)) ∞))

instance matrixOperatorProductCoeFun :
    CoeFun (MatrixOperatorProduct dims hd) (fun _ => (i : ι) → CMatrix (dims i)) where
  coe A := (show lp (fun i => CMatrix (dims i)) ∞ from A)

theorem matrixOperatorProduct_apply_norm_le (A : MatrixOperatorProduct dims hd) (i : ι) :
    matrixOpNorm (A i) ≤ ‖A‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero A i

noncomputable def matrixOperatorProductEquiv :
    MatrixOperatorProduct dims hd ≃⋆ₐ[ℂ] BoundedMatrixSequence dims where
  toFun A := ⟨fun i => A i, ‖A‖, norm_nonneg _, matrixOperatorProduct_apply_norm_le dims hd A⟩
  invFun A := ⟨A.val, memℓp_infty <| by
    obtain ⟨K, _, hK⟩ := BoundedMatrixSequence.bound dims A
    exact ⟨K, by rintro _ ⟨i, rfl⟩; exact hK i⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matrixOperatorProductEquiv_apply (A : MatrixOperatorProduct dims hd) (i : ι) :
    (matrixOperatorProductEquiv dims hd A).val i = A i := rfl

@[simp] theorem matrixOperatorProductEquiv_symm_apply (A : BoundedMatrixSequence dims) (i : ι) :
    (matrixOperatorProductEquiv dims hd).symm A i = A.val i := rfl

theorem matrixOperatorProduct_norm_le (A : MatrixOperatorProduct dims hd) (K : ℝ)
    (hK : 0 ≤ K) (hA : ∀ i, matrixOpNorm (A i) ≤ K) : ‖A‖ ≤ K :=
  lp.norm_le_of_forall_le hK hA

end ThomGame.Analysis
