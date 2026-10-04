module

public import ThomGame.Analysis.MatrixALTClassIsometries
public import ThomGame.Analysis.MatrixIsometryUnits

/-!
# Actual exact matrix units for the high equivalence classes

The entries are the products of the constructed isometries. Their
supports, adjoints, multiplication, nonvanishing, trace masses and
uniform fixing errors are all proved for these same matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

variable {d : Nat} [NeZero d]

theorem matrixIsometryUnit_fixed_error (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (U V : CMatrix d) (hU : matrixOpNorm U ≤ 1) (hV : matrixOpNorm V ≤ 1)
    (rho t : ℝ) (heU : matrixChannelEnergy F.toLinearMap U ≤ 36 * rho * t)
    (heV : matrixChannelEnergy F.toLinearMap V ≤ 36 * rho * t) :
    hsNorm (F (U * star V) - U * star V) ^ 2 ≤ 288 * rho * t := by
  have h := matrixUCP_product_fixed_error_sq F hF htrace U (star V) hU
    (by simpa only [matrixOpNorm_star] using hV)
  rw [matrixChannelEnergy_star] at h
  linarith

theorem exists_matrixALT_class_matrix_units {μ : Type*} [Fintype μ] [DecidableEq μ]
    (F : CMatrix d →CP CMatrix d) (hF : F 1 = 1)
    (htrace : ∀ Z, normalizedTrace (F Z) = normalizedTrace Z)
    (hpair : ∀ X Y, normalizedTrace (star (F X) * Y) = normalizedTrace (star X * F Y))
    (E : μ → CMatrix d) (hE : ∀ i, IsStarProjection (E i)) (hne : ∀ i, E i ≠ 0)
    (horth : Pairwise (fun i j => E i * E j = 0))
    (hbimod : ∀ A X B, A ∈ matrixPartitionScalarAlgebra E → B ∈ matrixPartitionScalarAlgebra E →
      F (A * X * B) = A * F X * B)
    (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 1024)
    (hsigma : matrixScalarMixingError E F.toLinearMap ≤ rho ^ 4) (S : Finset μ)
    (hbands : ∀ a ∈ S, ∀ b ∈ S, ∀ (lam : ℝ) (X : CMatrix d),
      X ≠ 0 → E a * X = X → X * E b = X → F X = (lam : ℂ) • X →
      (-rho ≤ lam ∧ lam ≤ rho) ∨ (1 - rho ≤ lam ∧ lam ≤ 1)) :
    ∃ (o : S → S) (q : S → CMatrix d) (W : S → S → CMatrix d),
      (∀ i j, matrixRectangleHasHighEigenvalue F.toLinearMap (E i.val) (E j.val) rho ↔ o i = o j) ∧
      (∀ i j, o i = o j → (E (o i).val).rank ≤ (E j.val).rank) ∧
      (∀ i, o (o i) = o i) ∧ (∀ i, q (o i) = E (o i).val) ∧
      (∀ i, IsStarProjection (q i) ∧ q i ≤ E i.val ∧ (q i).rank = (E (o i).val).rank ∧
        (normalizedTrace (q i)).re = (normalizedTrace (E (o i).val)).re ∧
        (1 - 2 * rho) * (normalizedTrace (E i.val)).re ≤ (normalizedTrace (q i)).re) ∧
      (∀ i, W i i = q i) ∧ (∀ i j, star (W i j) = W j i) ∧
      (∀ i j, E i.val * W i j = W i j ∧ W i j * E j.val = W i j) ∧
      (∀ i j, W i j ≠ 0 ↔ o i = o j) ∧
      (∀ i j k l, o i = o j →
        W i j * W k l = if j = k then W i l else 0) ∧
      (∀ i j, o i = o j → hsNorm (W i j) ^ 2 = (normalizedTrace (q i)).re ∧
        matrixOpNorm (W i j) ≤ 1 ∧
        hsNorm (F (W i j) - W i j) ^ 2 ≤ 288 * rho * (normalizedTrace (q i)).re) := by
  classical
  obtain ⟨o, U, _, hiff, hmin, hid, hdiag, hU⟩ := exists_matrixALT_class_isometries
    F hF htrace hpair E hE hne hbimod rho hrho hsmall hsigma S hbands
  let q := fun i => U i * star (U i)
  let W := fun i j => U i * star (U j)
  have hleft i := (hU i).1
  have hright i := (hU i).2.1
  have hgram i := (hU i).2.2.1
  have hproj i := (hU i).2.2.2.1
  have hnorm i := (hU i).2.2.2.2.2.2.1
  have henergy i := (hU i).2.2.2.2.2.2.2.1
  have htraceq i : (normalizedTrace (q i)).re = (normalizedTrace (E (o i).val)).re := by
    change (normalizedTrace (U i * star (U i))).re = _
    rw [normalizedTrace_mul_comm, hgram i]
  have horthS : Pairwise (fun i j : S => E i.val * E j.val = 0) := by
    intro i j hij
    exact horth (fun h => hij (Subtype.ext h))
  have hzero i j (hij : o i ≠ o j) : W i j = 0 :=
    matrixIsometryUnit_zero_of_initial_orthogonal (hE (o j).val) (hright i) (hright j) (horthS hij)
  refine ⟨o, q, W, hiff, hmin, hid, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change U (o i) * star (U (o i)) = E (o i).val
    rw [hdiag i, (hE (o i).val).isSelfAdjoint.star_eq, (hE (o i).val).isIdempotentElem.eq]
  · intro i
    obtain ⟨_, _, _, hp, hle, hrank, _, _, hmass⟩ := hU i
    exact ⟨hp, hle, hrank, htraceq i, by rw [htraceq i]; exact hmass⟩
  · exact matrixIsometryUnit_star U
  · exact matrixIsometryUnit_support (fun i : S => E i.val) U (fun i => hE i.val) hleft
  · intro i j
    refine ⟨fun hn => by_contra (fun h => hn (hzero i j h)), ?_⟩
    intro hij
    apply matrixIsometryUnit_nonzero (E (o i).val) (U i) (U j) (hE (o i).val) (hne (o i).val)
      (hgram i)
    · rw [hij]
      exact hgram j
    · rw [hij]
      exact hright j
  · intro i j k l hij
    exact matrixIsometryUnit_mul (fun i : S => E i.val) (fun i => E (o i).val) U
      (fun i => hE i.val) horthS hleft hright hgram i j k l (congrArg (fun a : S => E a.val) hij)
  · intro i j hij
    have heq : E (o j).val = E (o i).val := congrArg (fun a : S => E a.val) hij.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [htraceq i]
      exact matrixIsometryUnit_mass (E (o i).val) (U i) (U j) (hgram i)
        ((hgram j).trans heq) (by rw [← heq]; exact hright j)
    · exact (matrixOpNorm_mul_le _ _).trans (by
        rw [matrixOpNorm_star]
        nlinarith [hnorm i, hnorm j, matrixOpNorm_nonneg (U i), matrixOpNorm_nonneg (U j)])
    · rw [htraceq i]
      exact matrixIsometryUnit_fixed_error F hF htrace (U i) (U j) (hnorm i) (hnorm j)
        rho (normalizedTrace (E (o i).val)).re (henergy i) (by rw [← heq]; exact henergy j)

end ThomGame.Analysis
