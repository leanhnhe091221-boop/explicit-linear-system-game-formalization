module

public import ThomGame.Analysis.MatrixMarkovDiagonalExpectation

/-!
# Coordinate boundary energy and the quotient Poincare inequality

The explicit normalized commutator energy is continuous and bounded
by the squared Hilbert--Schmidt norm. It passes to the actual quotient.
The spectral gap controls the distance to the relative-commutant
expectation with the precise Poincare constant.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder

section Matrix

variable {d h : Nat} (U : Fin h → UnitaryMatrix d)

noncomputable def matrixCoordinateEnergy (X : CMatrix d) : ℝ :=
  lazyMarkovWeight h * ∑ j, hsNorm ((U j).val * X - X * (U j).val) ^ 2

theorem matrixCoordinateEnergy_nonneg (X : CMatrix d) : 0 ≤ matrixCoordinateEnergy U X :=
  mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

variable [NeZero d]

theorem continuous_hsNorm : Continuous (hsNorm : CMatrix d → ℝ) := by
  simpa only [matrixMapToHilbert_apply, LinearMap.id_apply, finiteMatrixHilbert_norm] using
    (matrixMapToHilbert (LinearMap.id : CMatrix d →ₗ[ℂ] CMatrix d)).continuous.norm

theorem matrixCoordinateEnergy_continuous : Continuous (matrixCoordinateEnergy U) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro j _
  exact ((continuous_hsNorm.comp ((continuous_const.mul continuous_id).sub
    (continuous_id.mul continuous_const))).pow 2)

variable [NeZero h]

theorem matrixCoordinateEnergy_le_hsNorm_sq (X : CMatrix d) :
    matrixCoordinateEnergy U X ≤ hsNorm X ^ 2 := by
  have hp := (Complex.nonneg_iff.mp (matrixLazyMarkov_trace_positive U X)).1
  rw [matrixLazyMarkov_pairing] at hp
  rw [matrixCoordinateEnergy, ← matrixLazyMarkov_energy, mul_sub, normalizedTrace_sub,
    Complex.sub_re, normalizedTrace_gram, Complex.ofReal_re]
  linarith

theorem matrixCoordinateEnergy_sqrt_le_hsNorm (X : CMatrix d) :
    Real.sqrt (matrixCoordinateEnergy U X) ≤ hsNorm X :=
  (Real.sqrt_le_iff).mpr ⟨hsNorm_nonneg X, matrixCoordinateEnergy_le_hsNorm_sq U X⟩

end Matrix

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem meanProjection_defect_pairing (T : H →L[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    inner ℂ (x - meanProjection T x) ((1 - T) (x - meanProjection T x)) =
      inner ℂ x ((1 - T) x) := by
  have he : (1 - T) (x - meanProjection T x) = (1 - T) x := by
    simp only [sub_apply, one_apply_eq_self, map_sub, meanProjection_fixed]
    abel
  have hz : inner ℂ (meanProjection T x) ((1 - T) x) = 0 := by
    have hi : inner ℂ (T (meanProjection T x)) x = inner ℂ (meanProjection T x) (T x) :=
      hs.isSymmetric (meanProjection T x) x
    rw [sub_apply, one_apply_eq_self, inner_sub_right,
      ← hi, meanProjection_fixed, sub_self]
  rw [he, inner_sub_left, hz, sub_zero]

end Hilbert

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i) (L : Ultrafilter ι)

omit [NeZero h] in
theorem matrixCoordinateEnergy_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => matrixCoordinateEnergy (U i) (A.val i)) (L : Filter ι)
      (𝓝 (matrixMarkovEnergy dims U hd L (matrixQuotientMk dims (L : Filter ι) A))) :=
  matrixMarkovEnergy_tendsto dims U hd L A

theorem matrixMarkovEnergy_hilbert (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixMarkovEnergy dims U hd L x =
      (inner ℂ (matrixHilbertEmbedding dims hd L x)
        ((1 - (matrixUniformLazyMarkov dims U hd).hilbertMap hd L) (matrixHilbertEmbedding dims hd L x))).re := by
  rw [sub_apply, one_apply_eq_self, UniformMatrixMap.hilbertMap_embedding, ← map_sub,
    matrixHilbertEmbedding_inner]
  exact (matrixQuotientLazyMarkov_energy dims U hd L x).symm

section NatIndex

variable (dims : Nat → Nat) (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

theorem matrixRelativeExpectation_energy_zero (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixMarkovEnergy dims U hd L (matrixRelativeExpectation dims U hd L hL x) = 0 :=
  (matrixMarkovEnergy_eq_zero_iff dims U hd L _).mpr
    ((mem_matrixRelativeCommutant_iff dims U (L : Filter Nat) _).mp
      (matrixRelativeExpectation_mem dims U hd L hL x))

theorem matrixRelativeExpectation_residual_energy (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixMarkovEnergy dims U hd L (x - matrixRelativeExpectation dims U hd L hL x) =
      matrixMarkovEnergy dims U hd L x := by
  rw [matrixMarkovEnergy_hilbert, matrixMarkovEnergy_hilbert, map_sub, matrixRelativeExpectation_embedding]
  exact congrArg Complex.re (meanProjection_defect_pairing _
    (matrixLazyMarkov_hilbertMap_selfAdjoint dims U hd L) _)

variable (κ : ℝ) (hgap : MatrixMarkovSpectralGap dims U hd L κ)

include hgap in
theorem matrixRelativeExpectation_poincare_sq (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    κ * ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ^ 2 ≤
      matrixMarkovEnergy dims U hd L x := by
  have hm : matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x) ∈
      (matrixRelativeCommutantTraceSubspace dims U hd L)ᗮ := by
    rw [map_sub, matrixRelativeExpectation_embedding,
      matrixMarkovProjection_eq_relativeCommutantProjection dims U hd L hL]
    exact (matrixRelativeCommutantTraceSubspace dims U hd L).sub_starProjection_mem_orthogonal _
  have he := hgap.2.2 _ hm
  rw [← matrixMarkovEnergy_hilbert, matrixRelativeExpectation_residual_energy] at he
  exact he

include hgap in
theorem matrixRelativeExpectation_poincare (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ≤
      (Real.sqrt κ)⁻¹ * Real.sqrt (matrixMarkovEnergy dims U hd L x) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hgap.1
  have he := matrixRelativeExpectation_poincare_sq dims U hd L hL κ hgap x
  have hb : Real.sqrt κ * ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ≤
      Real.sqrt (matrixMarkovEnergy dims U hd L x) := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hgap.1.le, Real.sq_sqrt (matrixMarkovEnergy_nonneg dims U hd L x)]
    exact he
  simpa only [inv_mul_cancel_left₀ hs.ne'] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hs.le)

end NatIndex
end ThomGame.Analysis
