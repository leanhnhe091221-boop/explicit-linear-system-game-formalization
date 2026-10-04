module

public import ThomGame.Analysis.MatrixClosedLowSpectralCut

/-!
# Finite-family interfaces for ALT Lemmas 3.2 and 3.3

A finite family is extended by zero, so no projection hypothesis on an
infinite tail is imposed on callers. The terminal sum is exactly the
sum of the given finite family.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d n h : Nat}

noncomputable def matrixExtendFiniteFamily (F : Fin n → CMatrix d) (i : Nat) : CMatrix d :=
  if hi : i < n then F ⟨i, hi⟩ else 0

@[simp] theorem matrixExtendFiniteFamily_apply (F : Fin n → CMatrix d) (i : Fin n) :
    matrixExtendFiniteFamily F i = F i := by simp [matrixExtendFiniteFamily, i.isLt]

theorem matrixExtendFiniteFamily_projection (F : Fin n → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (i : Nat) :
    IsStarProjection (matrixExtendFiniteFamily F i) := by
  unfold matrixExtendFiniteFamily
  split_ifs
  · exact hF _
  · exact IsStarProjection.zero (CMatrix d)

theorem matrixExtendFiniteFamily_sum {α : Type*} [AddCommMonoid α]
    (F : Fin n → CMatrix d) (f : CMatrix d → α) :
    (∑ i ∈ Finset.range n, f (matrixExtendFiniteFamily F i)) = ∑ i, f (F i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (matrixExtendFiniteFamily F i))]
  simp only [matrixExtendFiniteFamily_apply]

theorem matrixExtendFiniteFamily_total (P : CMatrix d) (F : Fin n → CMatrix d) :
    matrixProjectionPartialSum P (matrixExtendFiniteFamily F) n = P + ∑ i, F i := by
  rw [matrixProjectionPartialSum]
  congr 1
  simpa only [id_eq] using matrixExtendFiniteFamily_sum F id

theorem matrixResolvent_unitary_finite_family_bound [NeZero d] {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (F : Fin n → CMatrix d) (hF : ∀ i, IsStarProjection (F i))
    (U : UnitaryMatrix d) :
    (∑ i : Fin n, hsNorm ((U.val * matrixPositiveResolvent lam
      (matrixProjectionPartialSum 0 (matrixExtendFiniteFamily F) i) -
        matrixPositiveResolvent lam (matrixProjectionPartialSum 0 (matrixExtendFiniteFamily F) i) * U.val) * F i) ^ 2) ≤
      (292 / lam ^ 3) * (∑ i, hsNorm (U.val * F i - F i * U.val) ^ 2) := by
  have he := matrixResolvent_unitary_family_bound hlam hlam1 (matrixExtendFiniteFamily F)
    (matrixExtendFiniteFamily_projection F hF) U n
  rw [matrixExtendFiniteFamily_sum F (fun X => hsNorm (U.val * X - X * U.val) ^ 2)] at he
  rw [← Fin.sum_univ_eq_sum_range (fun i => hsNorm ((U.val * matrixPositiveResolvent lam
    (matrixProjectionPartialSum 0 (matrixExtendFiniteFamily F) i) -
      matrixPositiveResolvent lam (matrixProjectionPartialSum 0 (matrixExtendFiniteFamily F) i) * U.val) *
        matrixExtendFiniteFamily F i) ^ 2)] at he
  simpa only [matrixExtendFiniteFamily_apply] using he

theorem exists_matrixFiniteProjectionFamily_ALT_lemma3_3 [NeZero d] [NeZero h] {γ : ℝ} {e : CMatrix d}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (he : IsStarProjection e)
    (F : Fin n → CMatrix d) (hF : ∀ i, IsStarProjection (F i)) (U : Fin h → UnitaryMatrix d)
    (htrace : (normalizedTrace (1 - e)).re + (∑ i, (normalizedTrace (F i)).re) ≤ 3)
    (henergy : matrixCoordinateEnergy U (1 - e) + (∑ i, matrixCoordinateEnergy U (F i)) ≤ γ ^ 16) :
    ∃ Q : Fin n → CMatrix d,
      (∀ i, IsStarProjection (Q i) ∧ (Q i).rank ≤ (F i).rank) ∧
      (∑ i, matrixCoordinateEnergy U (Q i)) ≤ 100 * γ ^ 2 ∧
      (∑ i : Fin n, (normalizedTrace
        (matrixProjectionPartialSum (1 - e) (matrixExtendFiniteFamily F) i ^ 2 * Q i)).re) ≤ 3 * γ ∧
      matrixFamilyCoverageDefect Q ≤ (normalizedTrace (1 - e)).re +
        (normalizedTrace (matrixClosedLowSpectralCut ((1 - e) + ∑ i, F i) γ)).re + 7 * γ := by
  have ht : (normalizedTrace (1 - e)).re +
      (∑ i ∈ Finset.range n, (normalizedTrace (matrixExtendFiniteFamily F i)).re) ≤ 3 := by
    rw [matrixExtendFiniteFamily_sum F (fun X => (normalizedTrace X).re)]
    exact htrace
  have hE : matrixCoordinateEnergy U (1 - e) +
      (∑ i ∈ Finset.range n, matrixCoordinateEnergy U (matrixExtendFiniteFamily F i)) ≤ γ ^ 16 := by
    rw [matrixExtendFiniteFamily_sum F (matrixCoordinateEnergy U)]
    exact henergy
  obtain ⟨Q, hp, hq, hw, hc⟩ := exists_matrixProjectionFamily_ALT_lemma3_3 hγ hγ4 he
    (matrixExtendFiniteFamily F) (matrixExtendFiniteFamily_projection F hF) U n ht hE
  simp only [matrixExtendFiniteFamily_apply] at hp
  rw [matrixExtendFiniteFamily_total] at hc
  exact ⟨Q, hp, hq, hw, hc⟩

end ThomGame.Analysis
