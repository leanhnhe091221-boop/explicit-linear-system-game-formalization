module

public import ThomGame.Analysis.MatrixRandomSignSums
public import ThomGame.Analysis.MatrixOrthogonalProjectionEnergy

/-!
# Random signs detect the full off-block defect

For arbitrary complex matrices, the mean squared commutator with the
diagonal sign unitaries equals twice the squared pinching defect.
All norms retain the original ambient trace normalization.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq ι]

omit [Fintype μ] [DecidableEq ι] in
theorem matrixTraceReal_projection_commutator_cross (r : Nat) (X : Matrix ι ι ℂ)
    {q : Matrix ι ι ℂ} (hq : IsStarProjection q) :
    matrixTraceReal r ((X * q)ᴴ * (q * X)) =
      matrixTraceReal r ((q * X * q)ᴴ * (q * X * q)) := by
  calc
    _ = matrixTraceReal r (((X * q)ᴴ * (q * X)) * q) := by
      rw [matrixTraceReal_mul_comm r ((X * q)ᴴ * (q * X)) q]
      simp only [Matrix.conjTranspose_mul, hq.isSelfAdjoint.isHermitian.eq,
        ← Matrix.mul_assoc, hq.isIdempotentElem.eq]
    _ = _ := by
      rw [show q * X * q = q * (X * q) from Matrix.mul_assoc _ _ _,
        matrixProjection_compression_gram hq]
      simp only [Matrix.mul_assoc]

omit [Fintype μ] [DecidableEq ι] in
theorem rectHSNorm_projection_commutator_sq (r : Nat) (X : Matrix ι ι ℂ)
    {q : Matrix ι ι ℂ} (hq : IsStarProjection q) :
    rectHSNorm r (X * q - q * X) ^ 2 =
      rectHSNorm r (X * q) ^ 2 + rectHSNorm r (q * X) ^ 2 -
        2 * rectHSNorm r (q * X * q) ^ 2 := by
  rw [rectHSNorm_sub_sq, matrixTraceReal_projection_commutator_cross r X hq]
  simp only [matrixTraceReal_gram]

theorem rectHSNorm_pinching_commutator_sum (r : Nat) (E : μ → Matrix ι ι ℂ)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : Matrix ι ι ℂ) :
    (∑ i, rectHSNorm r (X * E i - E i * X) ^ 2) =
      2 * rectHSNorm r (X - matrixBlockPinch E X) ^ 2 := by
  have hleft := rectHSNorm_projection_sum_mul_sq r E hE horth X
  have hright := rectHSNorm_mul_projection_sum_sq r E hE horth X
  rw [hsum, Matrix.one_mul] at hleft
  rw [hsum, Matrix.mul_one] at hright
  have hcorner : rectHSNorm r (matrixBlockPinch E X) ^ 2 =
      ∑ i, rectHSNorm r (E i * X * E i) ^ 2 :=
    rectHSNorm_corner_sum_sq r E _ hE horth (fun i => by
      simp only [← Matrix.mul_assoc, (hE i).isIdempotentElem.eq])
  simp_rw [rectHSNorm_projection_commutator_sq r X (hE _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← hleft, ← hright, ← hcorner, rectHSNorm_pinching_defect_gram r E hE horth]
  simp only [matrixTraceReal_gram]
  ring

variable {d : Nat}

omit [Fintype ι] [DecidableEq ι] in
theorem matrixSignSum_unitary (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (ε : μ → Bool) : finiteSignSum E ε ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have hs := (matrixSignSum_selfAdjoint E hE ε).star_eq
  have hm : finiteSignSum E ε * finiteSignSum E ε = 1 :=
    (matrixSignSum_sq E hE horth ε).trans hsum
  exact ⟨by simpa only [hs] using hm, by simpa only [hs] using hm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem matrixSignSum_expect_pinching_commutator [NeZero d] [DecidableEq μ] (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    (𝔼 ε : μ → Bool, hsNorm (X * finiteSignSum E ε - finiteSignSum E ε * X) ^ 2) =
      2 * hsNorm (X - matrixBlockPinch E X) ^ 2 := by
  classical
  rw [show (fun ε : μ → Bool => hsNorm (X * finiteSignSum E ε - finiteSignSum E ε * X) ^ 2) =
    (fun ε => hsNorm (finiteSignSum (fun i => X * E i - E i * X) ε) ^ 2) from
      funext fun ε => by rw [matrixSignSum_commutator]]
  rw [matrixSignSum_expect_hsNorm_sq]
  simpa only [rectHSNorm_eq_hsNorm] using rectHSNorm_pinching_commutator_sum d E hE horth hsum X

omit [Fintype ι] [DecidableEq ι] in
theorem exists_matrixSignSum_pinching_defect_le [NeZero d] (E : μ → CMatrix d)
    (hE : ∀ i, IsStarProjection (E i)) (horth : Pairwise (fun i j => E i * E j = 0))
    (hsum : ∑ i, E i = 1) (X : CMatrix d) :
    ∃ ε : μ → Bool, 2 * hsNorm (X - matrixBlockPinch E X) ^ 2 ≤
      hsNorm (X * finiteSignSum E ε - finiteSignSum E ε * X) ^ 2 := by
  classical
  obtain ⟨ε, _, hε⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (le_of_eq (matrixSignSum_expect_pinching_commutator E hE horth hsum X).symm)
  exact ⟨ε, hε⟩

end ThomGame.Analysis
