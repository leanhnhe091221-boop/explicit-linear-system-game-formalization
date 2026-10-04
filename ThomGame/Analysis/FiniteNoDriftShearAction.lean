module

public import ThomGame.Analysis.FiniteNoDriftRecovery

/-! Both signed shear actions preserve the complete root alphabet with length at most four. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_coefficient_surj (m : Compressor.Coeff) : ∃ i, finiteNoDriftCoefficient i = m := by
  cases m with
  | none => exact ⟨0, rfl⟩
  | some p =>
    rcases p with ⟨c, b⟩
    fin_cases c <;> cases b
    · exact ⟨4, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨3, rfl⟩

theorem finiteNoDrift_full_cyclic_comm (f : Compressor.Generator → UnitaryMatrix d)
    (X : CMatrix d) {b : ℝ} (hb : 0 ≤ b)
    (hE : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X) ≤ b)
    (c : Fin 3) (m : Compressor.Coeff) :
    finiteNoDriftComm (f (.inl (Compressor.cyclicRoot c, m))) X ≤ 2 * Real.sqrt 234375 * b := by
  obtain ⟨i, rfl⟩ := finiteNoDrift_coefficient_surj m
  obtain ⟨j, hj⟩ := finiteNoDriftRootTuple_generator f finiteNoDriftCoefficient c i
  have hs := finiteNoDriftEnergy_single (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X j
  rw [hj] at hs
  have he := finiteNoDriftEnergy_sq_bound (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X hE
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.cast_ofNat] at hs
  apply (sq_le_sq₀ (finiteNoDriftComm_nonneg _ _) (by positivity)).mp
  have hh : (2 * Real.sqrt (234375 : ℝ) * b) ^ 2 = 937500 * b ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 234375)]
    ring
  rw [hh]
  nlinarith

theorem finiteNoDrift_full_initial_comm (f : Compressor.Generator → UnitaryMatrix d) {δ b : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hE : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftCoefficient) X) ≤ b)
    (r : Compressor.Root) (m : Compressor.Coeff) :
    finiteNoDriftComm (f (.inl (r, m))) X ≤ 8 * Real.sqrt 234375 * b + 2 * δ := by
  have hc := finiteNoDrift_full_cyclic_comm f X hb hE
  rcases finiteNoDrift_root_geometry r with hr | hr
  · have hh := hc (Compressor.source r) m
    rw [← hr] at hh
    nlinarith [Real.sqrt_nonneg (234375 : ℝ)]
  · have he := finiteNoDrift_e2_dist f hf (Compressor.cyclicRoot (Compressor.source r)) m
    rw [← hr, unitaryDist_comm] at he
    have ht := finiteNoDriftComm_close (f (.inl (r, m)))
      (f (.inl (Compressor.cyclicRoot (Compressor.source r), m)) *
        f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none)) *
        (f (.inl (Compressor.cyclicRoot (Compressor.source r), m)))⁻¹ *
        (f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none)))⁻¹) X hX
    have hbr := finiteNoDriftComm_bracket (f (.inl (Compressor.cyclicRoot (Compressor.source r), m)))
      (f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none))) X
    have h₁ := hc (Compressor.source r) m
    have h₂ := hc (finRotate 3 (Compressor.source r)) none
    rw [finiteNoDrift_right_cyclic] at ht hbr he
    linarith

theorem finiteNoDrift_signed_action_dist (f : Compressor.Generator → UnitaryMatrix d) {δ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (s r : Compressor.Root) (m : Compressor.Coeff) (ε : Bool) :
    unitaryDist ((if ε then f (.inr s) else (f (.inr s))⁻¹) * f (.inl (r, m)) *
      (if ε then f (.inr s) else (f (.inr s))⁻¹)⁻¹)
      (Word.eval f (Compressor.actionTarget s r ε m)) ≤ δ := by
  have hmem : Word.equation (Compressor.conjugate (Compressor.signed (Compressor.shear s) ε)
      (Compressor.X r m)) (Compressor.actionTarget s r ε m) ∈ Compressor.actionRelations := by
    exact List.mem_flatMap.mpr ⟨s, Compressor.mem_roots s,
      List.mem_flatMap.mpr ⟨ε, by cases ε <;> simp,
        List.mem_flatMap.mpr ⟨r, Compressor.mem_roots r,
          List.mem_map.mpr ⟨m, Compressor.mem_coefficients m, rfl⟩⟩⟩⟩
  have hm : Word.equation (Compressor.conjugate (Compressor.signed (Compressor.shear s) ε)
      (Compressor.X r m)) (Compressor.actionTarget s r ε m) ∈ Compressor.rawRelators := by
    simp only [Compressor.rawRelators, List.mem_append]
    tauto
  have he := finiteNoDrift_equation_dist f _ _ (hf _ hm)
  cases ε <;> simpa only [Compressor.conjugate, Compressor.signed, Bool.false_eq_true, ↓reduceIte,
    Word.eval_append, Word.eval_inverse, Compressor.X, Compressor.shear, Word.eval_generator] using he

theorem finiteNoDrift_all_action_comm (f : Compressor.Generator → UnitaryMatrix d)
    (X : CMatrix d) {a : ℝ} (ha : 0 ≤ a)
    (hroot : ∀ r m, finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (s r : Compressor.Root) (m : Compressor.Coeff) (ε : Bool) :
    finiteNoDriftComm (Word.eval f (Compressor.actionTarget s r ε m)) X ≤ 4 * a := by
  cases m with
  | none =>
    simp only [Compressor.actionTarget, Compressor.X, Word.eval_generator]
    have h := hroot r none
    linarith
  | some p =>
    rcases p with ⟨c, b⟩
    simp only [Compressor.actionTarget]
    split_ifs
    · simp only [Word.eval_commutator, Compressor.X, Word.eval_generator]
      have h := finiteNoDriftComm_bracket (f (.inl (Compressor.across r, some (c, b))))
        (f (.inl (Compressor.reverse (Compressor.right r), some (Compressor.source s, Compressor.signMul ε b)))) X
      have h₁ := hroot (Compressor.across r) (some (c, b))
      have h₂ := hroot (Compressor.reverse (Compressor.right r)) (some (Compressor.source s, Compressor.signMul ε b))
      linarith
    · simp only [Compressor.X, Word.eval_generator]
      have h := hroot r (some (c, b))
      linarith

theorem finiteNoDrift_signed_pullback_comm (f : Compressor.Generator → UnitaryMatrix d) {δ a : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (ha : 0 ≤ a)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hroot : ∀ r m, finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (s r : Compressor.Root) (m : Compressor.Coeff) (ε : Bool) :
    finiteNoDriftComm (f (.inl (r, m)))
      (matrixUnitaryConjugation ((if ε then f (.inr s) else (f (.inr s))⁻¹)⁻¹) X) ≤ 4 * a + 2 * δ := by
  let U := if ε then f (.inr s) else (f (.inr s))⁻¹
  simp only [matrixUnitaryConjugation_apply, Matrix.UnitaryGroup.inv_val, star_star]
  change finiteNoDriftComm (f (.inl (r, m))) (U.valᴴ * X * U.val) ≤ _
  rw [finiteNoDriftComm_pullback]
  have h₁ := finiteNoDriftComm_close (U * f (.inl (r, m)) * U⁻¹)
    (Word.eval f (Compressor.actionTarget s r ε m)) X hX
  have h₂ := finiteNoDrift_signed_action_dist f hf s r m ε
  have h₃ := finiteNoDrift_all_action_comm f X ha hroot s r m ε
  change unitaryDist (U * f (.inl (r, m)) * U⁻¹) _ ≤ δ at h₂
  linarith

end ThomGame.Analysis
