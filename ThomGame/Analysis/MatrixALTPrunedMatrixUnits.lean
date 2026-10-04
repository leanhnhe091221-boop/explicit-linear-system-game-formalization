module

public import ThomGame.Analysis.MatrixALTRetainedEquivalence
public import ThomGame.Analysis.MatrixALTClassMatrixUnits
public import ThomGame.Analysis.MatrixSubprojectionTraceLoss

/-!
# Pruned exact matrix units with a uniform total support bound

The original channel and its two small defects suffice: pruning,
the high relation, minimum-rank representatives and the actual matrix
units are constructed. Spectral bands are not additional premises.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem exists_matrixALT_pruned_matrix_units {μ : Type*} [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ X, normalizedTrace (F X) = normalizedTrace X)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0)) (hsum : ∑ i, E i = 1)
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 < rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4)
    (hdelta : matrixMixedNorm (F.toLinearMap.comp F.toLinearMap - F.toLinearMap) ≤ rho ^ 4) :
    ∃ S : Finset μ, ∃ (o : S → S) (q : S → CMatrix d) (W : S → S → CMatrix d),
      IsStarProjection (∑ i : S, E i.val) ∧
      (normalizedTrace (1 - ∑ i : S, E i.val)).re ≤ 64 * rho ^ 2 ∧
      (∀ i ∈ S, ∀ j ∈ S, ∀ (lam : ℝ) (X : CMatrix d),
        X ≠ 0 → E i * X = X → X * E j = X → F X = (lam : ℂ) • X →
        (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) ∧
      IsStarProjection (∑ i, q i) ∧ (∑ i, q i) ≤ (∑ i : S, E i.val) ∧
      (normalizedTrace (1 - ∑ i, q i)).re ≤ 64 * rho ^ 2 + 2 * rho ∧
      (∀ i j, matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho ↔ o i = o j) ∧
      (∀ i j, o i = o j → (E (o i).val).rank ≤ (E j.val).rank) ∧
      (∀ i, o (o i) = o i) ∧ (∀ i, q (o i) = E (o i).val) ∧
      (∀ i, IsStarProjection (q i) ∧ q i ≤ E i.val ∧ (q i).rank = (E (o i).val).rank ∧
        (normalizedTrace (q i)).re = (normalizedTrace (E (o i).val)).re ∧
        (1 - 2 * rho) * (normalizedTrace (E i.val)).re ≤ (normalizedTrace (q i)).re) ∧
      (∀ i, W i i = q i) ∧ (∀ i j, star (W i j) = W j i) ∧
      (∀ i j, E i.val * W i j = W i j ∧ W i j * E j.val = W i j) ∧
      (∀ i j, W i j ≠ 0 ↔ o i = o j) ∧
      (∀ i j k l, o i = o j → W i j * W k l = if j = k then W i l else 0) ∧
      (∀ i j, o i = o j → hsNorm (W i j) ^ 2 = (normalizedTrace (q i)).re ∧
        matrixOpNorm (W i j) ≤ 1 ∧
        hsNorm (F (W i j) - W i j) ^ 2 ≤ 288 * rho * (normalizedTrace (q i)).re) := by
  obtain ⟨B, p, _, hpsum, hp, hpmass, hbands⟩ := exists_matrixALT_retained_projection
    F hF htrace hpair E hE hne horth hsum hbimod rho hrho (by linarith) hsigma hdelta
  let S := Finset.univ \ B
  have hb : ∀ a ∈ S, ∀ b ∈ S, ∀ (lam : ℝ) (X : CMatrix d),
      X ≠ 0 → E a * X = X → X * E b = X → F X = (lam : ℂ) • X →
      (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1) := by
    intro a ha b hb
    exact hbands a (Finset.mem_sdiff.mp ha).2 b (Finset.mem_sdiff.mp hb).2
  obtain ⟨o, q, W, hiff, hmin, hid, hdiag, hq, hWdiag, hstar, hsupport, hneW, hmul, herror⟩ :=
    exists_matrixALT_class_matrix_units F hF htrace hpair E hE hne horth hbimod
      rho hrho.le hsmall hsigma S hb
  have hpS : p = ∑ i : S, E i.val := by
    rw [Finset.sum_coe_sort]
    exact hpsum
  have horthS : Pairwise (fun i j : S => E i.val * E j.val = 0) := by
    intro i j hij
    exact horth (fun h => hij (Subtype.ext h))
  obtain ⟨hqsum, hle, hloss⟩ := matrixSubprojection_sum_trace_loss (fun i : S => E i.val) q
    (fun i => hE i.val) (fun i => (hq i).1) horthS (fun i => (hq i).2.1)
      (2 * rho) (by positivity) (fun i => (hq i).2.2.2.2)
  rw [hpS] at hp hpmass
  exact ⟨S, o, q, W, hp, hpmass, hb, hqsum, hle, hloss.trans (add_le_add hpmass le_rfl),
    hiff, hmin, hid, hdiag, hq, hWdiag, hstar, hsupport, hneW, hmul, herror⟩

end ThomGame.Analysis
