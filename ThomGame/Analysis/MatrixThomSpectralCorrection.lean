module

public import ThomGame.Analysis.MatrixStinespringAveraging
public import ThomGame.Analysis.MatrixStinespringReindex
public import ThomGame.Analysis.MatrixPartialIsometryCompression

/-!
# Actual relative averaging and spectral correction for Thom Proposition 3.1

Starting only with the original near inclusion, construct the two
commuting representations, their common isometry, the averaged positive
contraction and its closed half cut. The corrected dimension, deleted
mass and all exact common intertwining relations have the stated bounds.
Polar correction and comparison of the final algebras are subsequent steps.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d m : Nat}

theorem matrixIsometry_cut_loss_le_distance (r : Nat) (V : Matrix (Fin m) (Fin d) ℂ)
    (hV : Vᴴ * V = 1) (Q : CMatrix m) :
    rectHSNorm r ((1 - Q) * V) ^ 2 ≤ rectHSNorm r (V * Vᴴ - Q) ^ 2 := by
  have he : (1 - Q) * V = (V * Vᴴ - Q) * V := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [he]
  apply rectHSNorm_mul_sq_le_of_partialIsometry
  rw [hV]
  exact IsStarProjection.one _

variable [NeZero d]

structure MatrixThomSpectralData (A B D : StarSubalgebra ℂ (CMatrix d)) (ε : ℝ) where
  sourceRep : CMatrix d →⋆ₐ[ℂ] CMatrix (d * (d * d))
  commutantRep : CMatrix d →⋆ₐ[ℂ] CMatrix (d * (d * d))
  source_injective : Function.Injective sourceRep
  representations_commute : ∀ X Y, sourceRep X * commutantRep Y = commutantRep Y * sourceRep X
  isometry : Matrix (Fin (d * (d * d))) (Fin d) ℂ
  isometry_gram : isometryᴴ * isometry = 1
  expectation : ∀ X, isometryᴴ * sourceRep X * isometry = matrixTraceProjection A X
  common_intertwines : ∀ X ∈ D, sourceRep X * isometry = isometry * X
  commutant_intertwines : ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
    commutantRep X * isometry = isometry * X
  average : CMatrix (d * (d * d))
  average_eq : average = matrixTraceProjection
    (StarSubalgebra.centralizer ℂ ((B.map sourceRep) : Set (CMatrix (d * (d * d))))) (isometry * isometryᴴ)
  average_nonneg : 0 ≤ average
  average_le_one : average ≤ 1
  average_trace : matrixTraceReal d average = 1
  variance_identity : matrixTraceReal d (average - average * average) =
    rectHSNorm d (isometry * isometryᴴ - average) ^ 2
  variance_le : rectHSNorm d (isometry * isometryᴴ - average) ^ 2 ≤ ε ^ 2
  cut : CMatrix (d * (d * d))
  cut_eq : cut = matrixHalfProjection average
  cut_projection : IsStarProjection cut
  cut_commutes_source : ∀ X ∈ B, cut * sourceRep X = sourceRep X * cut
  average_commutes_commutant : ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
    average * commutantRep X = commutantRep X * average
  cut_commutes_commutant : ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
    cut * commutantRep X = commutantRep X * cut
  cut_distance_le : rectHSNorm d (isometry * isometryᴴ - cut) ^ 2 ≤ 2 * ε ^ 2
  dimension_error : |(cut.rank : ℝ) / d - 1| ≤ 2 * ε ^ 2
  deleted_mass_le : rectHSNorm d ((1 - cut) * isometry) ^ 2 ≤ 2 * ε ^ 2
  cut_common_intertwines : ∀ X ∈ D, sourceRep X * (cut * isometry) = (cut * isometry) * X
  cut_commutant_intertwines : ∀ X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d)),
    commutantRep X * (cut * isometry) = (cut * isometry) * X

theorem exists_matrixThomSpectralData (A B D : StarSubalgebra ℂ (CMatrix d))
    (hDA : D ≤ A) (hDB : D ≤ B) {ε : ℝ} (hε : 0 ≤ ε) (hBA : MatrixNearInclusion B A ε) :
    Nonempty (MatrixThomSpectralData A B D ε) := by
  obtain ⟨ρ, σ, hρ, hcomm, V, hV, hE, hA, hC⟩ := exists_matrixRelativeStinespring_fin A
  obtain ⟨h, Q, heq, h0, h1, htrace, hvariance, hv, hQeq, hQ, hQC, hdist, hdim, hexact⟩ :=
    exists_matrixStinespring_averaged_cut A B hε hBA ρ hρ V hV hE
  have hσC (X : CMatrix d) : σ X ∈ StarSubalgebra.centralizer ℂ
      ((B.map ρ) : Set (CMatrix (d * (d * d)))) := by
    apply (mem_matrixSubalgebraCommutant_iff (B.map ρ) (σ X)).mpr
    intro Z hZ
    have hz : ∃ Y ∈ B, ρ Y = Z := hZ
    obtain ⟨Y, _, rfl⟩ := hz
    exact hcomm Y X
  have hright (X : CMatrix d) (hX : X ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))) :
      h * σ X = σ X * h ∧ Q * σ X = σ X * Q := by
    apply hexact (σ X) (hσC X)
    exact matrixStinespring_range_commutes σ V X (hC X hX)
      (hC (star X) ((StarSubalgebra.centralizer ℂ (A : Set (CMatrix d))).star_mem' hX))
  have hleft (X : CMatrix d) (hX : X ∈ B) : Q * ρ X = ρ X * Q :=
    ((mem_matrixSubalgebraCommutant_iff (B.map ρ) Q).mp hQC (ρ X) ⟨X, hX, rfl⟩).symm
  refine ⟨{
    sourceRep := ρ, commutantRep := σ, source_injective := hρ, representations_commute := hcomm
    isometry := V, isometry_gram := hV, expectation := hE
    common_intertwines := fun X hX => hA X (hDA hX), commutant_intertwines := hC
    average := h, average_eq := heq, average_nonneg := h0, average_le_one := h1, average_trace := htrace
    variance_identity := hvariance, variance_le := hv, cut := Q, cut_eq := hQeq, cut_projection := hQ
    cut_commutes_source := hleft, average_commutes_commutant := fun X hX => (hright X hX).1
    cut_commutes_commutant := fun X hX => (hright X hX).2, cut_distance_le := hdist
    dimension_error := ?_, deleted_mass_le := (matrixIsometry_cut_loss_le_distance d V hV Q).trans hdist
    cut_common_intertwines := ?_, cut_commutant_intertwines := ?_ }⟩
  · simpa only [matrixTraceReal_projection_rank d hQ] using hdim
  · intro X hX
    rw [← Matrix.mul_assoc, ← hleft X (hDB hX), Matrix.mul_assoc, hA X (hDA hX), Matrix.mul_assoc]
  · intro X hX
    rw [← Matrix.mul_assoc, ← (hright X hX).2, Matrix.mul_assoc, hC X hX, Matrix.mul_assoc]

theorem MatrixThomSpectralData.cut_rank_pos {A B D : StarSubalgebra ℂ (CMatrix d)}
    {ε : ℝ} (S : MatrixThomSpectralData A B D ε) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) : 0 < S.cut.rank := by
  by_contra hn
  have hz : S.cut.rank = 0 := Nat.eq_zero_of_not_pos hn
  have hd := S.dimension_error
  rw [hz, Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_one] at hd
  nlinarith

theorem MatrixThomSpectralData.dimension_error_absolute {A B D : StarSubalgebra ℂ (CMatrix d)}
    {ε : ℝ} (S : MatrixThomSpectralData A B D ε) :
    |(S.cut.rank : ℝ) - d| ≤ 2 * ε ^ 2 * d := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have he : (S.cut.rank : ℝ) / d - 1 = ((S.cut.rank : ℝ) - d) / d := by
    rw [sub_div, div_self (ne_of_gt hd)]
  have hb := S.dimension_error
  rw [he, abs_div, abs_of_pos hd] at hb
  exact (div_le_iff₀ hd).mp hb

end ThomGame.Analysis
