module

public import ThomGame.Analysis.MatrixLazyMarkov
public import ThomGame.Analysis.UniformMatrixNormTransfer

/-!
# Arbitrary coordinate powers of the actual lazy Markov maps

Every power is contractive in both norms. The exponent may vary with
the matrix coordinate and need not be bounded, so these maps meet the
proved uniform-transfer hypotheses for the diagonal powers used by ALT.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

section Matrix

variable {d h : Nat} [NeZero h] (U : Fin h → UnitaryMatrix d)

theorem matrixLazyMarkov_pow_matrixOpNorm_le (k : Nat) (X : CMatrix d) :
    matrixOpNorm ((matrixLazyMarkov U ^ k) X) ≤ matrixOpNorm X := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (matrixLazyMarkov_matrixOpNorm_le U _).trans ih

omit [NeZero h] in
theorem matrixLazyMarkov_pow_star (k : Nat) (X : CMatrix d) :
    (matrixLazyMarkov U ^ k) (star X) = star ((matrixLazyMarkov U ^ k) X) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, matrixLazyMarkov_star]

variable [NeZero d]

theorem matrixLazyMarkov_pow_hsNorm_le (k : Nat) (X : CMatrix d) :
    hsNorm ((matrixLazyMarkov U ^ k) X) ≤ hsNorm X := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (matrixLazyMarkov_hsNorm_le U _).trans ih

omit [NeZero h] in
theorem matrixLazyMarkov_pow_hilbert (k : Nat) (X : CMatrix d) :
    finiteMatrixHilbertEquiv d ((matrixLazyMarkov U ^ k) X) =
      (lazyHilbertAverage (fun j => matrixConjugationHilbertEquiv (U j)) ^ k) (finiteMatrixHilbertEquiv d X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, mul_apply_eq_comp, matrixLazyMarkov_hilbert, ih]

@[simp] theorem matrixLazyMarkov_pow_one (k : Nat) : (matrixLazyMarkov U ^ k) 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, matrixLazyMarkov_one]

@[simp] theorem matrixLazyMarkov_pow_trace (k : Nat) (X : CMatrix d) :
    normalizedTrace ((matrixLazyMarkov U ^ k) X) = normalizedTrace X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, matrixLazyMarkov_trace, ih]

end Matrix

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i)

noncomputable def matrixUniformMarkovPower (k : ι → Nat) : UniformMatrixMap dims := by
  let : ∀ i, NeZero (dims i) := fun i => ⟨Nat.ne_of_gt (hd i)⟩
  exact {
    toLinearMap i := matrixLazyMarkov (U i) ^ k i
    operatorBound := 1
    hilbertBound := 1
    operator_le i X := by simpa only [NNReal.coe_one, one_mul] using
      matrixLazyMarkov_pow_matrixOpNorm_le (U i) (k i) X
    hilbert_le i X := by simpa only [NNReal.coe_one, one_mul] using
      matrixLazyMarkov_pow_hsNorm_le (U i) (k i) X }

@[simp] theorem matrixUniformMarkovPower_apply (k : ι → Nat) (i : ι) (X : CMatrix (dims i)) :
    (matrixUniformMarkovPower dims U hd k).toLinearMap i X = (matrixLazyMarkov (U i) ^ k i) X := rfl

noncomputable def matrixUniformLazyMarkov : UniformMatrixMap dims :=
  matrixUniformMarkovPower dims U hd (fun _ => 1)

@[simp] theorem matrixUniformLazyMarkov_apply (i : ι) (X : CMatrix (dims i)) :
    (matrixUniformLazyMarkov dims U hd).toLinearMap i X = matrixLazyMarkov (U i) X := by
  change (matrixLazyMarkov (U i) ^ 1) X = _
  rw [pow_one]

theorem matrixUniformMarkovPower_hilbertNorm_le (k : ι → Nat) (L : Ultrafilter ι) :
    ‖(matrixUniformMarkovPower dims U hd k).hilbertMap hd L‖ ≤ 1 :=
  (matrixUniformMarkovPower dims U hd k).hilbertMap_norm_le hd L

theorem matrixUniformMarkovPower_sequence_one (k : ι → Nat) :
    (matrixUniformMarkovPower dims U hd k).sequenceMap 1 = 1 := by
  apply Subtype.ext
  funext i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixLazyMarkov_pow_one (U i) (k i)

theorem matrixUniformMarkovPower_sequence_star (k : ι → Nat) (A : BoundedMatrixSequence dims) :
    (matrixUniformMarkovPower dims U hd k).sequenceMap (star A) =
      star ((matrixUniformMarkovPower dims U hd k).sequenceMap A) := by
  apply Subtype.ext
  funext i
  exact matrixLazyMarkov_pow_star (U i) (k i) (A.val i)

theorem matrixUniformMarkovPower_quotient_one (k : ι → Nat) (L : Filter ι) :
    (matrixUniformMarkovPower dims U hd k).quotientMap L 1 = 1 := by
  rw [← map_one (matrixQuotientMk dims L), UniformMatrixMap.quotientMap_mk,
    matrixUniformMarkovPower_sequence_one, map_one]

theorem matrixUniformMarkovPower_quotient_star (k : ι → Nat) (L : Filter ι)
    (x : MatrixTracialQuotient dims L) :
    (matrixUniformMarkovPower dims U hd k).quotientMap L (star x) =
      star ((matrixUniformMarkovPower dims U hd k).quotientMap L x) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  rw [matrixQuotientMk_star, UniformMatrixMap.quotientMap_mk, matrixUniformMarkovPower_sequence_star,
    ← matrixQuotientMk_star, UniformMatrixMap.quotientMap_mk]

theorem matrixUniformMarkovPower_sequence_trace (k : ι → Nat) (A : BoundedMatrixSequence dims) (i : ι) :
    normalizedTrace (((matrixUniformMarkovPower dims U hd k).sequenceMap A).val i) = normalizedTrace (A.val i) := by
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  exact matrixLazyMarkov_pow_trace (U i) (k i) (A.val i)

theorem matrixUniformMarkovPower_quotient_trace (k : ι → Nat) (L : Ultrafilter ι)
    (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixUltratrace dims hd L ((matrixUniformMarkovPower dims U hd k).quotientMap (L : Filter ι) x) =
      matrixUltratrace dims hd L x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (L : Filter ι) x
  change matrixSequenceUltratrace dims L ((matrixUniformMarkovPower dims U hd k).sequenceMap A) =
    matrixSequenceUltratrace dims L A
  unfold matrixSequenceUltratrace
  simp only [matrixUniformMarkovPower_sequence_trace]

end ThomGame.Analysis
