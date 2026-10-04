module

public import ThomGame.Analysis.UnitaryHilbertSchmidt

/-!
# The exact rank-one involution example

diag(-1,1,...,1) is a nonidentity unitary involution in every positive
dimension. Its normalized distance to the identity is exactly 2/sqrt(d),
so these nonidentity matrices approach the identity as dimension grows.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped Matrix.Norms.Frobenius Topology

variable (d : Nat) [NeZero d]

def rankOneMatrix : CMatrix d := diagonal (fun i => if i = 0 then -1 else 1)

theorem rankOneMatrix_star : star (rankOneMatrix d) = rankOneMatrix d := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [rankOneMatrix, hi]
  · simp [rankOneMatrix, hij, Ne.symm hij]

theorem rankOneMatrix_square : rankOneMatrix d * rankOneMatrix d = 1 := by
  rw [rankOneMatrix, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [hi]
  · simp [hij]

def rankOneUnitary : UnitaryMatrix d :=
  ⟨rankOneMatrix d, by
    change star (rankOneMatrix d) * rankOneMatrix d = 1 ∧
      rankOneMatrix d * star (rankOneMatrix d) = 1
    rw [rankOneMatrix_star]
    exact ⟨rankOneMatrix_square d, rankOneMatrix_square d⟩⟩

@[simp] theorem rankOneUnitary_square : rankOneUnitary d * rankOneUnitary d = 1 :=
  Subtype.ext (rankOneMatrix_square d)

@[simp] theorem rankOneUnitary_inv : (rankOneUnitary d)⁻¹ = rankOneUnitary d :=
  inv_eq_of_mul_eq_one_left (rankOneUnitary_square d)

theorem rankOneUnitary_ne_one : rankOneUnitary d ≠ 1 := by
  intro he
  have h := congrArg (fun U : UnitaryMatrix d => U.val 0 0) he
  norm_num [rankOneUnitary, rankOneMatrix] at h

theorem rankOneMatrix_sub_one : rankOneMatrix d - 1 =
    diagonal (fun i : Fin d => if i = 0 then (-2 : ℂ) else 0) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> norm_num [rankOneMatrix, hi]
  · simp [rankOneMatrix, hij]

theorem unitaryLength_rankOne : unitaryLength (rankOneUnitary d) = 2 / Real.sqrt d := by
  change hsNorm (rankOneMatrix d - 1) = _
  rw [rankOneMatrix_sub_one, hsNorm, frobenius_eq_sqrt_entries]
  simp [Matrix.diagonal_apply, apply_ite]

end ThomGame.Analysis
