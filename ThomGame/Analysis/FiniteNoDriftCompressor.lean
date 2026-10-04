module

public import ThomGame.Analysis.FiniteNoDriftRootEnergy

/-! The finite presentation supplies the commutator estimates used by no drift. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem finiteNoDrift_positive_coeff (i : Fin 4) (r : Compressor.Root) :
    Compressor.positive (.inl (r, finiteNoDriftPositiveCoefficient i)) = true := by
  fin_cases i <;> rfl

theorem finiteNoDrift_positive_coeff_surj (r : Compressor.Root) (m : Compressor.Coeff)
    (hm : Compressor.positive (.inl (r, m)) = true) : ∃ i, finiteNoDriftPositiveCoefficient i = m := by
  cases m with
  | none => exact ⟨0, rfl⟩
  | some p =>
    rcases p with ⟨c, b⟩
    cases b
    · contradiction
    · fin_cases c
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩

theorem finiteNoDrift_root_geometry (r : Compressor.Root) :
    r = Compressor.cyclicRoot (Compressor.source r) ∨
      r = Compressor.across (Compressor.cyclicRoot (Compressor.source r)) := by
  revert r
  decide +kernel

theorem finiteNoDrift_right_cyclic (c : Fin 3) :
    Compressor.right (Compressor.cyclicRoot c) = Compressor.cyclicRoot (finRotate 3 c) := by
  revert c
  decide +kernel

variable {d : Nat} [NeZero d]

theorem finiteNoDrift_positive_comm (f : Compressor.Generator → UnitaryMatrix d) {δ τ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hE : Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient) X) ≤ τ)
    (r : Compressor.Root) (m : Compressor.Coeff) (hm : Compressor.positive (.inl (r, m)) = true) :
    finiteNoDriftComm (f (.inl (r, m))) X ≤ 350 * τ + 2 * δ := by
  obtain ⟨i, rfl⟩ := finiteNoDrift_positive_coeff_surj r m hm
  have hc := finiteNoDrift_positive_cyclic_comm f X hτ hE
  rcases finiteNoDrift_root_geometry r with hr | hr
  · have hh := hc (Compressor.source r) i
    rw [← hr] at hh
    linarith
  · have he := finiteNoDrift_e2_dist f hf (Compressor.cyclicRoot (Compressor.source r))
      (finiteNoDriftPositiveCoefficient i)
    rw [← hr, unitaryDist_comm] at he
    have ht := finiteNoDriftComm_close (f (.inl (r, finiteNoDriftPositiveCoefficient i)))
      (f (.inl (Compressor.cyclicRoot (Compressor.source r), finiteNoDriftPositiveCoefficient i)) *
        f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none)) *
        (f (.inl (Compressor.cyclicRoot (Compressor.source r), finiteNoDriftPositiveCoefficient i)))⁻¹ *
        (f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none)))⁻¹) X hX
    have hb := finiteNoDriftComm_bracket
      (f (.inl (Compressor.cyclicRoot (Compressor.source r), finiteNoDriftPositiveCoefficient i)))
      (f (.inl (Compressor.right (Compressor.cyclicRoot (Compressor.source r)), none))) X
    have h₁ := hc (Compressor.source r) i
    have h₂ := hc (finRotate 3 (Compressor.source r)) 0
    rw [finiteNoDrift_right_cyclic] at ht hb he
    change finiteNoDriftComm (f (.inl (Compressor.cyclicRoot (finRotate 3 (Compressor.source r)), none))) X ≤ _ at h₂
    linarith

theorem finiteNoDriftComm_pullback (U G : UnitaryMatrix d) (X : CMatrix d) :
    finiteNoDriftComm G (U.valᴴ * X * U.val) = finiteNoDriftComm (U * G * U⁻¹) X := by
  have hu : U.val * U.valᴴ = 1 := U.prop.2
  have he : U.val * (G.val * (U.valᴴ * X * U.val) - (U.valᴴ * X * U.val) * G.val) * U.valᴴ =
      (U * G * U⁻¹).val * X - X * (U * G * U⁻¹).val := by
    change U.val * (G.val * (U.valᴴ * X * U.val) - (U.valᴴ * X * U.val) * G.val) * U.valᴴ =
      U.val * G.val * U.valᴴ * X - X * (U.val * G.val * U.valᴴ)
    rw [mul_sub, sub_mul]
    have h₁ : U.val * (G.val * (U.valᴴ * X * U.val)) * U.valᴴ = U.val * G.val * U.valᴴ * X := by
      calc
        _ = (U.val * G.val * U.valᴴ * X) * (U.val * U.valᴴ) := by simp only [mul_assoc]
        _ = _ := by rw [hu, mul_one]
    have h₂ : U.val * ((U.valᴴ * X * U.val) * G.val) * U.valᴴ = X * (U.val * G.val * U.valᴴ) := by
      calc
        _ = (U.val * U.valᴴ) * (X * (U.val * G.val * U.valᴴ)) := by simp only [mul_assoc]
        _ = _ := by rw [hu, one_mul]
    rw [h₁, h₂]
  unfold finiteNoDriftComm
  rw [← he]
  change hsNorm _ = hsNorm (U.val * _ * (U⁻¹).val)
  rw [hsNorm_mul_unitary, hsNorm_unitary_mul]

theorem finiteNoDrift_positive_action_comm (f : Compressor.Generator → UnitaryMatrix d)
    (X : CMatrix d) {a : ℝ} (ha : 0 ≤ a)
    (hpos : ∀ r m, Compressor.positive (.inl (r, m)) = true → finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (s r : Compressor.Root) (m : Compressor.Coeff) (hm : Compressor.positive (.inl (r, m)) = true) :
    finiteNoDriftComm (Word.eval f (Compressor.actionTarget s r true m)) X ≤ 4 * a := by
  cases m with
  | none =>
    simp only [Compressor.actionTarget, Compressor.X, Word.eval_generator]
    have h := hpos r none rfl
    linarith
  | some p =>
    rcases p with ⟨c, b⟩
    cases b
    · contradiction
    · simp only [Compressor.actionTarget]
      split_ifs
      · simp only [Word.eval_commutator, Compressor.X, Word.eval_generator, Compressor.signMul, ↓reduceIte]
        have h := finiteNoDriftComm_bracket (f (.inl (Compressor.across r, some (c, true))))
          (f (.inl (Compressor.reverse (Compressor.right r), some (Compressor.source s, true)))) X
        have h₁ := hpos (Compressor.across r) (some (c, true)) rfl
        have h₂ := hpos (Compressor.reverse (Compressor.right r)) (some (Compressor.source s, true)) rfl
        linarith
      · simp only [Compressor.X, Word.eval_generator]
        have h := hpos r (some (c, true)) rfl
        linarith

theorem finiteNoDrift_forward_energy (f : Compressor.Generator → UnitaryMatrix d) {δ a : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (X : CMatrix d) (hX : matrixOpNorm X ≤ 1)
    (hpos : ∀ r m, Compressor.positive (.inl (r, m)) = true → finiteNoDriftComm (f (.inl (r, m))) X ≤ a)
    (s : Compressor.Root) :
    Real.sqrt (matrixCoordinateEnergy (finiteNoDriftRootTuple f finiteNoDriftPositiveCoefficient)
      ((f (.inr s)).valᴴ * X * (f (.inr s)).val)) ≤ 32 * a + 16 * δ := by
  have hh := finiteNoDriftRootEnergy_max f finiteNoDriftPositiveCoefficient
    ((f (.inr s)).valᴴ * X * (f (.inr s)).val) (by positivity : 0 ≤ 4 * a + 2 * δ) (fun c i => by
      rw [finiteNoDriftComm_pullback]
      have h₁ := finiteNoDriftComm_close
        (f (.inr s) * f (.inl (Compressor.cyclicRoot c, finiteNoDriftPositiveCoefficient i)) * (f (.inr s))⁻¹)
        (Word.eval f (Compressor.actionTarget s (Compressor.cyclicRoot c) true (finiteNoDriftPositiveCoefficient i))) X hX
      have h₂ := finiteNoDrift_action_dist f hf s (Compressor.cyclicRoot c) (finiteNoDriftPositiveCoefficient i)
      have h₃ := finiteNoDrift_positive_action_comm f X ha hpos s (Compressor.cyclicRoot c)
        (finiteNoDriftPositiveCoefficient i) (finiteNoDrift_positive_coeff i _)
      linarith)
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hh
  linarith

end ThomGame.Analysis
