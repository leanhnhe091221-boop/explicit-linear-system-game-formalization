module

public import ThomGame.Analysis.MatrixMarkovPowers
public import ThomGame.Analysis.UniformMatrixMapOrder

/-!
# Markov energy and the relative commutant in the actual tracial quotient

The coordinate energy identity passes to the actual ultralimit. The
resulting positive sum vanishes exactly when every commutator vanishes.
A sharp defect estimate proves that these are precisely the fixed
elements of the induced Markov map, without any internality premise.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology BigOperators

variable {ι : Type*} (dims : ι → Nat) {h : Nat} [NeZero h]
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i)) (hd : ∀ i, 0 < dims i)

omit [NeZero h] in
def matrixTupleClass (L : Filter ι) (j : Fin h) : MatrixTracialQuotient dims L :=
  matrixQuotientMk dims L (boundedUnitarySequence dims (fun i => U i j))

noncomputable def matrixQuotientLazyMarkov (L : Filter ι) :
    MatrixTracialQuotient dims L →ₗ[ℂ] MatrixTracialQuotient dims L :=
  (matrixUniformLazyMarkov dims U hd).quotientMap L

@[simp] theorem matrixQuotientLazyMarkov_mk (L : Filter ι) (A : BoundedMatrixSequence dims) :
    matrixQuotientLazyMarkov dims U hd L (matrixQuotientMk dims L A) =
      matrixQuotientMk dims L ((matrixUniformLazyMarkov dims U hd).sequenceMap A) := rfl

variable (L : Ultrafilter ι)

noncomputable def matrixMarkovEnergy (x : MatrixTracialQuotient dims (L : Filter ι)) : ℝ :=
  lazyMarkovWeight h * ∑ j, ‖matrixHilbertEmbedding dims hd L
    (matrixTupleClass dims U (L : Filter ι) j * x - x * matrixTupleClass dims U (L : Filter ι) j)‖ ^ 2

omit [NeZero h] in
theorem matrixMarkovEnergy_nonneg (x : MatrixTracialQuotient dims (L : Filter ι)) :
    0 ≤ matrixMarkovEnergy dims U hd L x :=
  mul_nonneg (lazyMarkovWeight_nonneg h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [NeZero h] in
theorem matrixMarkovEnergy_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => lazyMarkovWeight h * ∑ j, hsNorm ((U i j).val * A.val i - A.val i * (U i j).val) ^ 2)
      (L : Filter ι) (𝓝 (matrixMarkovEnergy dims U hd L (matrixQuotientMk dims (L : Filter ι) A))) := by
  apply Filter.Tendsto.const_mul
  apply tendsto_finsetSum
  intro j _
  let C : BoundedMatrixSequence dims := boundedUnitarySequence dims (fun i => U i j) * A -
    A * boundedUnitarySequence dims (fun i => U i j)
  have ht := (matrixHilbertEmbedding_norm_tendsto dims hd L C).pow 2
  change Tendsto (fun i => hsNorm ((U i j).val * A.val i - A.val i * (U i j).val) ^ 2)
    (L : Filter ι) (𝓝 (‖matrixHilbertEmbedding dims hd L (matrixQuotientMk dims (L : Filter ι) C)‖ ^ 2)) at ht
  simpa only [C, map_sub, map_mul, matrixTupleClass] using ht

theorem matrixQuotientLazyMarkov_pairing_tendsto (A : BoundedMatrixSequence dims) :
    Tendsto (fun i => (normalizedTrace (star (A.val i) * (A.val i - matrixLazyMarkov (U i) (A.val i)))).re)
      (L : Filter ι) (𝓝 (matrixUltratrace dims hd L
        (star (matrixQuotientMk dims (L : Filter ι) A) *
          (matrixQuotientMk dims (L : Filter ι) A - matrixQuotientLazyMarkov dims U hd (L : Filter ι)
            (matrixQuotientMk dims (L : Filter ι) A)))).re) := by
  rw [matrixQuotientLazyMarkov_mk, matrixQuotientMk_star, ← map_sub, ← map_mul, matrixUltratrace_mk]
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (matrixSequenceUltratrace_tendsto dims hd L
      (star A * (A - (matrixUniformLazyMarkov dims U hd).sequenceMap A)))
  change Tendsto (fun i => (normalizedTrace (star (A.val i) *
      (A.val i - (matrixUniformLazyMarkov dims U hd).toLinearMap i (A.val i)))).re)
    (L : Filter ι) (𝓝 (matrixSequenceUltratrace dims L
      (star A * (A - (matrixUniformLazyMarkov dims U hd).sequenceMap A))).re) at ht
  simpa only [matrixUniformLazyMarkov_apply] using ht

theorem matrixQuotientLazyMarkov_energy (x : MatrixTracialQuotient dims (L : Filter ι)) :
    (matrixUltratrace dims hd L (star x * (x - matrixQuotientLazyMarkov dims U hd (L : Filter ι) x))).re =
      matrixMarkovEnergy dims U hd L x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (L : Filter ι) x
  apply tendsto_nhds_unique (matrixQuotientLazyMarkov_pairing_tendsto dims U hd L A)
  have he (i : ι) : (normalizedTrace (star (A.val i) * (A.val i - matrixLazyMarkov (U i) (A.val i)))).re =
      lazyMarkovWeight h * ∑ j, hsNorm ((U i j).val * A.val i - A.val i * (U i j).val) ^ 2 := by
    let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
    exact matrixLazyMarkov_energy (U i) (A.val i)
  simpa only [he] using matrixMarkovEnergy_tendsto dims U hd L A

theorem matrixQuotientLazyMarkov_defect_norm_sq_le (x : MatrixTracialQuotient dims (L : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd L (x - matrixQuotientLazyMarkov dims U hd (L : Filter ι) x)‖ ^ 2 ≤
      matrixMarkovEnergy dims U hd L x := by
  rw [← matrixQuotientLazyMarkov_energy]
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (L : Filter ι) x
  have hl := (matrixHilbertEmbedding_norm_tendsto dims hd L
    (A - (matrixUniformLazyMarkov dims U hd).sequenceMap A)).pow 2
  have hr := matrixQuotientLazyMarkov_pairing_tendsto dims U hd L A
  rw [map_sub, ← matrixQuotientLazyMarkov_mk] at hl
  apply le_of_tendsto_of_tendsto' hl hr
  intro i
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  change hsNorm (A.val i - (matrixUniformLazyMarkov dims U hd).toLinearMap i (A.val i)) ^ 2 ≤ _
  simpa only [matrixUniformLazyMarkov_apply] using
    matrixLazyMarkov_defect_norm_sq_le (U i) (A.val i)

theorem matrixMarkovEnergy_eq_zero_iff (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixMarkovEnergy dims U hd L x = 0 ↔ ∀ j, Commute (matrixTupleClass dims U (L : Filter ι) j) x := by
  constructor
  · intro he
    have hs : (∑ j, ‖matrixHilbertEmbedding dims hd L
        (matrixTupleClass dims U (L : Filter ι) j * x - x * matrixTupleClass dims U (L : Filter ι) j)‖ ^ 2) = 0 :=
      (mul_eq_zero.mp he).resolve_left (ne_of_gt (lazyMarkovWeight_pos h))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg
      ‖matrixHilbertEmbedding dims hd L
        (matrixTupleClass dims U (L : Filter ι) j * x - x * matrixTupleClass dims U (L : Filter ι) j)‖)).mp hs
    intro j
    apply sub_eq_zero.mp
    apply matrixHilbertEmbedding_injective dims hd L
    simpa only [map_zero] using norm_eq_zero.mp (sq_eq_zero_iff.mp (hz j (Finset.mem_univ j)))
  · intro hc
    have hz (j : Fin h) : matrixTupleClass dims U (L : Filter ι) j * x -
        x * matrixTupleClass dims U (L : Filter ι) j = 0 := sub_eq_zero.mpr (hc j).eq
    simp only [matrixMarkovEnergy, hz, map_zero, norm_zero, zero_pow (by decide : (2 : Nat) ≠ 0),
      Finset.sum_const_zero, mul_zero]

theorem matrixQuotientLazyMarkov_fixed_iff (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixQuotientLazyMarkov dims U hd (L : Filter ι) x = x ↔
      ∀ j, Commute (matrixTupleClass dims U (L : Filter ι) j) x := by
  rw [← matrixMarkovEnergy_eq_zero_iff dims U hd L x]
  constructor
  · intro hx
    rw [← matrixQuotientLazyMarkov_energy, hx, sub_self, mul_zero, matrixUltratrace_zero, Complex.zero_re]
  · intro he
    have hb := matrixQuotientLazyMarkov_defect_norm_sq_le dims U hd L x
    rw [he] at hb
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _)))
    symm
    apply sub_eq_zero.mp
    apply matrixHilbertEmbedding_injective dims hd L
    simpa only [map_zero] using hz

theorem matrixLazyMarkov_hilbertMap_nonneg :
    0 ≤ (matrixUniformLazyMarkov dims U hd).hilbertMap hd L := by
  apply UniformMatrixMap.hilbertMap_nonneg_of_trace_positive
  intro i X
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  simpa only [matrixUniformLazyMarkov_apply] using matrixLazyMarkov_trace_positive (U i) X

theorem matrixLazyMarkov_hilbertMap_le_one :
    (matrixUniformLazyMarkov dims U hd).hilbertMap hd L ≤ 1 := by
  apply UniformMatrixMap.hilbertMap_le_one_of_trace_defect_positive
  intro i X
  let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
  simpa only [matrixUniformLazyMarkov_apply] using matrixLazyMarkov_trace_defect_positive (U i) X

theorem matrixLazyMarkov_hilbertMap_selfAdjoint :
    IsSelfAdjoint ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L) :=
  (ContinuousLinearMap.nonneg_iff_isPositive.mp (matrixLazyMarkov_hilbertMap_nonneg dims U hd L)).isSelfAdjoint

section NatIndex

variable (dims : Nat → Nat) (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

theorem matrixFiniteLazyMarkov_fixed_iff (T : MatrixFiniteOperatorAlgebra dims hd L) :
    (matrixUniformLazyMarkov dims U hd).finiteMap hd L hL T = T ↔
      ∀ j, Commute (matrixFiniteEmbedding dims hd L (matrixTupleClass dims U (L : Filter Nat) j)) T := by
  obtain ⟨x, rfl⟩ := matrixFiniteEmbedding_surjective dims hd L hL T
  rw [UniformMatrixMap.finiteMap_embedding, (matrixFiniteEmbedding_injective dims hd L).eq_iff]
  change matrixQuotientLazyMarkov dims U hd (L : Filter Nat) x = x ↔ _
  rw [matrixQuotientLazyMarkov_fixed_iff]
  apply forall_congr'
  intro j
  change _ ↔ matrixFiniteEmbedding dims hd L _ * matrixFiniteEmbedding dims hd L x =
    matrixFiniteEmbedding dims hd L x * matrixFiniteEmbedding dims hd L _
  rw [← map_mul, ← map_mul, (matrixFiniteEmbedding_injective dims hd L).eq_iff]
  rfl

end NatIndex

end ThomGame.Analysis
