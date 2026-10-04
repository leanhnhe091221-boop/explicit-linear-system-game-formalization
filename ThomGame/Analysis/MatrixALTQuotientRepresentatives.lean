module

public import ThomGame.Analysis.MatrixALTTheorem4_3
public import ThomGame.Analysis.MatrixNonzeroScalarPartition
public import ThomGame.Analysis.UnitarySequenceQuotient

/-!
# ALT representatives of the same ultraproduct elements

The squared-sum perturbation gives individual normalized HS convergence,
and hence equality both in the unitary sequence quotient and in the
actual tracial matrix quotient. All partition blocks can be chosen
nonzero and their number is at most the coordinate dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter Matrix
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem hsNorm_tendsto_zero_of_sum_sq {ι μ : Type*} [Fintype μ] (dims : ι → Nat) (L : Filter ι)
    (X : (k : ι) → μ → CMatrix (dims k))
    (hX : Tendsto (fun k => ∑ j, hsNorm (X k j) ^ 2) L (𝓝 0)) (j : μ) :
    Tendsto (fun k => hsNorm (X k j)) L (𝓝 0) := by
  have hs : Tendsto (fun k => hsNorm (X k j) ^ 2) L (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) (fun k =>
      Finset.single_le_sum (fun i _ => sq_nonneg (hsNorm (X k i))) (Finset.mem_univ j)) hX
  have he := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (hsNorm_nonneg _), Real.sqrt_zero] using he

theorem matrixQuotientMk_tuple_eq_of_sum_sq {ι : Type*} (dims : ι → Nat) (L : Filter ι) {h : Nat}
    (U V : (k : ι) → Fin h → UnitaryMatrix (dims k))
    (hUV : Tendsto (fun k => ∑ j, hsNorm ((U k j).val - (V k j).val) ^ 2) L (𝓝 0)) (j : Fin h) :
    matrixQuotientMk dims L (boundedUnitarySequence dims (fun k => U k j)) =
      matrixQuotientMk dims L (boundedUnitarySequence dims (fun k => V k j)) := by
  apply (matrixQuotientMk_eq_iff dims L _ _).mpr
  exact hsNorm_tendsto_zero_of_sum_sq dims L (fun k j => (U k j).val - (V k j).val) hUV j

theorem unitarySequenceMk_tuple_eq_of_sum_sq {ι : Type*} (dims : ι → Nat) (L : Filter ι) {h : Nat}
    (U V : (k : ι) → Fin h → UnitaryMatrix (dims k))
    (hUV : Tendsto (fun k => ∑ j, hsNorm ((U k j).val - (V k j).val) ^ 2) L (𝓝 0)) (j : Fin h) :
    unitarySequenceMk dims L (fun k => U k j) = unitarySequenceMk dims L (fun k => V k j) := by
  apply (unitarySequenceMk_eq_iff dims L _ _).mpr
  exact hsNorm_tendsto_zero_of_sum_sq dims L (fun k j => (U k j).val - (V k j).val) hUV j

theorem exists_matrixUltraproduct_ALT_nonzero_representatives (dims : Nat → Nat) {h : Nat} [NeZero h]
    (U : (k : Nat) → Fin h → UnitaryMatrix (dims k)) (hd : ∀ k, 0 < dims k)
    (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop) (κ : ℝ)
    (hgap : MatrixMarkovSpectralGap dims U hd L κ) :
    ∃ T : (k : Nat) → Fin (h + h) → UnitaryMatrix (dims k),
      ∃ Q : (k : Nat) → MatrixScalarGapPartition (T k) (κ ^ 2 / 2 ^ 28),
        (∀ k i, (Q k).E i ≠ 0) ∧ (∀ k, (Q k).n ≤ dims k) ∧
        Tendsto (fun k => ∑ j, hsNorm ((T k j).val - (Fin.append (U k) (U k) j).val) ^ 2)
          (L : Filter Nat) (𝓝 0) ∧
        (∀ j, matrixQuotientMk dims (L : Filter Nat) (boundedUnitarySequence dims (fun k => T k j)) =
          matrixQuotientMk dims (L : Filter Nat)
            (boundedUnitarySequence dims (fun k => Fin.append (U k) (U k) j))) ∧
        (∀ j, unitarySequenceMk dims (L : Filter Nat) (fun k => T k j) =
          unitarySequenceMk dims (L : Filter Nat) (fun k => Fin.append (U k) (U k) j)) := by
  obtain ⟨T, P, _, hlim⟩ := exists_matrixUltraproduct_ALT_decomposition dims U hd L hL κ hgap
  choose Q hne hn _ using fun k => (P k).exists_nonzero (T k)
  exact ⟨T, Q, hne, hn, hlim,
    matrixQuotientMk_tuple_eq_of_sum_sq dims (L : Filter Nat) T (fun k => Fin.append (U k) (U k)) hlim,
    unitarySequenceMk_tuple_eq_of_sum_sq dims (L : Filter Nat) T (fun k => Fin.append (U k) (U k)) hlim⟩

end ThomGame.Analysis
