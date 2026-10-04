module

public import ThomGame.Analysis.MatrixSubalgebraUnitaryCorrection
public import ThomGame.Analysis.MatrixUnitaryLifting
public import ThomGame.Analysis.MatrixInternalCommutants

/-!
# Exact unitary lifts in internal algebras and their commutants

Apply the subalgebra-preserving correction coordinatewise. Unitaries
in an internal algebra have representatives in its prescribed coordinate
unitary groups; unitaries in its commutant have exactly commuting lifts.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology

variable {ι : Type*} (dims : ι → Nat)
  (S : (k : ι) → StarSubalgebra ℂ (CMatrix (dims k))) (hd : ∀ k, 0 < dims k) (L : Filter ι)

include hd

theorem exists_internalUnitarySequence_close_of_gram (A : BoundedMatrixSequence dims)
    (hA : ∀ k, A.val k ∈ S k)
    (hgram : Tendsto (fun k => hsNorm ((A.val k)ᴴ * A.val k - 1)) L (𝓝 0)) :
    ∃ U : UnitarySequence dims, (∀ k, (U k).val ∈ S k) ∧
      Tendsto (fun k => hsNorm (A.val k - (U k).val)) L (𝓝 0) := by
  classical
  let (k : ι) : NeZero (dims k) := ⟨Nat.ne_of_gt (hd k)⟩
  choose U hUS hU using fun k => exists_matrixSubalgebraUnitary_close_of_gram (S k) (hA k)
  exact ⟨U, hUS, squeeze_zero (fun k => hsNorm_nonneg _) hU hgram⟩

theorem exists_matrixInternal_unitary_lift (u : unitary (MatrixTracialQuotient dims L))
    (hu : u.val ∈ matrixInternalQuotient dims S L) :
    ∃ U : UnitarySequence dims, (∀ k, (U k).val ∈ S k) ∧
      matrixQuotientMk dims L (boundedUnitarySequence dims U) = u.val := by
  obtain ⟨A, hAS, hA⟩ := (mem_matrixInternalQuotient dims S L u.val).mp hu
  have he : matrixQuotientMk dims L (star A * A) = matrixQuotientMk dims L 1 := by
    rw [map_mul, ← matrixQuotientMk_star, hA, map_one]
    exact u.property.1
  have hgram := (matrixQuotientMk_eq_iff dims L (star A * A) 1).mp he
  obtain ⟨U, hUS, hU⟩ := exists_internalUnitarySequence_close_of_gram dims S hd L A hAS hgram
  exact ⟨U, hUS, ((matrixQuotientMk_eq_iff dims L A (boundedUnitarySequence dims U)).mpr hU).symm.trans hA⟩

theorem exists_matrixInternalCommutant_unitary_lift (u : unitary (MatrixTracialQuotient dims L))
    (hu : u.val ∈ StarSubalgebra.centralizer ℂ
      (matrixInternalQuotient dims S L : Set (MatrixTracialQuotient dims L))) :
    ∃ U : UnitarySequence dims, (∀ k X, X ∈ S k → X * (U k).val = (U k).val * X) ∧
      matrixQuotientMk dims L (boundedUnitarySequence dims U) = u.val := by
  rw [matrixInternalQuotient_commutant dims S hd L] at hu
  obtain ⟨U, hUS, hU⟩ := exists_matrixInternal_unitary_lift dims
    (fun k => StarSubalgebra.centralizer ℂ (S k : Set (CMatrix (dims k)))) hd L u hu
  exact ⟨U, fun k => (mem_matrixSubalgebraCommutant_iff (S k) (U k).val).mp (hUS k), hU⟩

end ThomGame.Analysis
