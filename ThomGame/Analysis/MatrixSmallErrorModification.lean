module

public import ThomGame.Analysis.MatrixQuotientEventualEquality
public import ThomGame.Analysis.MatrixNearInclusion

/-!
# Scalar replacement at the exceptional large-error coordinates

The index set and all original dimensions stay fixed. Outside the actual
epsilon < 1/2 set, replace coordinate algebras by scalars and epsilon by
zero. The large-set invariance theorem identifies the original internal
algebras with the modified ones.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*}

noncomputable def matrixSmallError (ε : ι → ℝ) (i : ι) : ℝ :=
  if ε i < 1 / 2 then ε i else 0

noncomputable def matrixSmallErrorAlgebra (dims : ι → Nat)
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ) (i : ι) :
    StarSubalgebra ℂ (CMatrix (dims i)) := if ε i < 1 / 2 then C i else ⊥

theorem matrixSmallError_nonneg (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    0 ≤ matrixSmallError ε i := by
  unfold matrixSmallError
  split_ifs
  · exact hε i
  · exact le_rfl

theorem matrixSmallError_lt_half (ε : ι → ℝ) (i : ι) : matrixSmallError ε i < 1 / 2 := by
  unfold matrixSmallError
  split_ifs with hi
  · exact hi
  · norm_num

theorem matrixSmallErrorAlgebra_eq (dims : ι → Nat)
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)
    {i : ι} (hi : ε i < 1 / 2) : matrixSmallErrorAlgebra dims C ε i = C i := ite_eq_left hi

theorem matrixSmallErrorAlgebra_mono (dims : ι → Nat)
    (C E : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)
    (hCE : ∀ i, C i ≤ E i) (i : ι) :
    matrixSmallErrorAlgebra dims C ε i ≤ matrixSmallErrorAlgebra dims E ε i := by
  unfold matrixSmallErrorAlgebra
  split_ifs
  · exact hCE i
  · exact le_rfl

theorem matrixSmallError_nearInclusion (dims : ι → Nat)
    (A B : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ)
    (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) (i : ι) :
    MatrixNearInclusion (matrixSmallErrorAlgebra dims B ε i)
      (matrixSmallErrorAlgebra dims A ε i) (matrixSmallError ε i) := by
  unfold matrixSmallErrorAlgebra matrixSmallError
  split_ifs
  · exact hBA i
  · intro X hX _
    exact ⟨X, hX, by simp only [sub_self, hsNorm_zero, le_refl]⟩

theorem matrixSmallError_eventually_lt_half (ε : ι → ℝ) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) : ∀ᶠ i in L, ε i < 1 / 2 :=
  hε.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

theorem matrixSmallError_eventually_eq (ε : ι → ℝ) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) : matrixSmallError ε =ᶠ[L] ε :=
  (matrixSmallError_eventually_lt_half ε L hε).mono fun _ hi => ite_eq_left hi

theorem matrixSmallError_tendsto (ε : ι → ℝ) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) : Tendsto (matrixSmallError ε) L (𝓝 0) :=
  hε.congr' (matrixSmallError_eventually_eq ε L hε).symm

theorem matrixSmallErrorAlgebra_eventually_eq (dims : ι → Nat)
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) : ∀ᶠ i in L, matrixSmallErrorAlgebra dims C ε i = C i :=
  (matrixSmallError_eventually_lt_half ε L hε).mono fun _ hi => ite_eq_left hi

theorem matrixSmallErrorAlgebra_internal_eq (dims : ι → Nat)
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))) (ε : ι → ℝ) (L : Filter ι)
    (hε : Tendsto ε L (𝓝 0)) :
    matrixInternalQuotient dims (matrixSmallErrorAlgebra dims C ε) L = matrixInternalQuotient dims C L :=
  matrixInternalQuotient_eq_of_eventually_eq dims _ _ L (matrixSmallErrorAlgebra_eventually_eq dims C ε L hε)

end ThomGame.Analysis
