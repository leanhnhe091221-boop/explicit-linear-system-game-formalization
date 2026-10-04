module

public import ThomGame.Analysis.FiniteNoDriftEnergyCertificate
public import ThomGame.Groups.DoubleToLambda

/-! The actual two-copy action relations yield the final obstruction estimate. -/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat} [NeZero d]

theorem finiteNoDriftComm_double_difference (T V G : UnitaryMatrix d) :
    finiteNoDriftComm G (T⁻¹ * V).val = unitaryDist (T * G * T⁻¹) (V * G * V⁻¹) := by
  have h₁ : T * (G * (T⁻¹ * V)) * V⁻¹ = T * G * T⁻¹ := by group
  have h₂ : T * ((T⁻¹ * V) * G) * V⁻¹ = V * G * V⁻¹ := by group
  have he := unitaryDist_mul_right (T * (G * (T⁻¹ * V))) (T * ((T⁻¹ * V) * G)) V⁻¹
  rw [h₁, h₂, unitaryDist_mul_left] at he
  exact he.symm

theorem finiteNoDrift_action_agree (f g : Compressor.Generator → UnitaryMatrix d)
    (hfg : ∀ x, Compressor.positive x = true → f x = g x)
    (s r : Compressor.Root) (m : Compressor.Coeff) (hm : Compressor.positive (.inl (r, m)) = true) :
    Word.eval f (Compressor.actionTarget s r true m) = Word.eval g (Compressor.actionTarget s r true m) := by
  cases m with
  | none => simpa only [Compressor.actionTarget, Compressor.X, Word.eval_generator] using hfg (.inl (r, none)) rfl
  | some p =>
    rcases p with ⟨c, b⟩
    cases b
    · contradiction
    · simp only [Compressor.actionTarget]
      split_ifs
      · simp only [Word.eval_commutator, Compressor.X, Word.eval_generator, Compressor.signMul, ↓reduceIte]
        rw [hfg (.inl (Compressor.across r, some (c, true))) rfl,
          hfg (.inl (Compressor.reverse (Compressor.right r), some (Compressor.source s, true))) rfl]
      · simpa only [Compressor.X, Word.eval_generator] using hfg (.inl (r, some (c, true))) rfl

theorem finiteNoDrift_double_c_comm (f g : Compressor.Generator → UnitaryMatrix d) {δ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (hg : FiniteNoDriftCompressorModel g δ)
    (hfg : ∀ x, Compressor.positive x = true → f x = g x)
    (s r : Compressor.Root) (m : Compressor.Coeff) (hm : Compressor.positive (.inl (r, m)) = true) :
    finiteNoDriftComm (f (.inl (r, m))) ((f (.inr s))⁻¹ * g (.inr s)).val ≤ 2 * δ := by
  rw [finiteNoDriftComm_double_difference]
  have h₁ := finiteNoDrift_action_dist f hf s r m
  have h₂ := finiteNoDrift_action_dist g hg s r m
  rw [← hfg (.inl (r, m)) hm, ← finiteNoDrift_action_agree f g hfg s r m hm] at h₂
  have ht := unitaryDist_triangle
    (f (.inr s) * f (.inl (r, m)) * (f (.inr s))⁻¹)
    (Word.eval f (Compressor.actionTarget s r true m))
    (g (.inr s) * f (.inl (r, m)) * (g (.inr s))⁻¹)
  rw [unitaryDist_comm (Word.eval f _)] at ht
  linarith

noncomputable def finiteNoDriftDoubleCopy (f : MatrixAssignment Double.Generator d)
    (b : Bool) : Compressor.Generator → UnitaryMatrix d := fun g => f (FreeGroup.of (Double.copyGenerator b g))

theorem finiteNoDriftDoubleCopy_agree (f : MatrixAssignment Double.Generator d)
    (x : Compressor.Generator) (hx : Compressor.positive x = true) :
    finiteNoDriftDoubleCopy f false x = finiteNoDriftDoubleCopy f true x := by
  unfold finiteNoDriftDoubleCopy
  rw [Double.copy_positive_eq x hx]

/-- Four original finite energy certificates and the actual defining relators force
the named 72-generator obstruction word to have distance less than one quarter. -/
theorem finiteNoDrift_double_obstruction (f : MatrixAssignment Double.Generator d)
    (A D : StarSubalgebra ℂ (CMatrix d)) {τ δ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ 1 / (10 : ℝ) ^ 40)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / (10 : ℝ) ^ 40)
    (hf : IsApproxRepresentation Double.relators δ f)
    (E : FiniteNoDriftEnergyCertificates (finiteNoDriftDoubleCopy f false) A D τ) :
    unitaryLength (f (FreeGroup.mk Double.obstructionWord)) < 1 / 4 := by
  let f₀ := finiteNoDriftDoubleCopy f false
  let f₁ := finiteNoDriftDoubleCopy f true
  have hf₀ : FiniteNoDriftCompressorModel f₀ δ := finiteNoDrift_copy_model f hf false
  have hf₁ : FiniteNoDriftCompressorModel f₁ δ := finiteNoDrift_copy_model f hf true
  let j := (Fintype.equivFinOfCardEq Compressor.root_card) Compressor.root12
  let T := f₀ (.inr Compressor.root12)
  let V := f₁ (.inr Compressor.root12)
  let H := f₀ (.inl (Compressor.root12, some (1, true)))
  have hj : finiteNoDriftShearTuple f₀ j = T := finiteNoDriftShearTuple_at f₀ Compressor.root12
  have hc := finiteNoDrift_energy_c_distance f₀ A D hδ E (T⁻¹ * V)
    (fun r m hm => finiteNoDrift_double_c_comm f₀ f₁ hf₀ hf₁ (finiteNoDriftDoubleCopy_agree f)
      Compressor.root12 r m hm)
  have hH : ∀ X, X ∈ A → matrixOpNorm X ≤ 1 → hsNorm (X * H.val - H.val * X) ≤ 350 * τ + 2 * δ := by
    intro X hXA hX
    rw [hsNorm_sub_comm]
    exact finiteNoDrift_positive_comm f₀ hf₀ hδ hτ X hX (E.positive_energy X hXA hX)
      Compressor.root12 (some (1, true)) rfl
  have hbound := finiteNoDrift_finite_certificate A D (finiteNoDriftShearTuple f₀) j V H
    hτ hτsmall hδ hδsmall (finiteNoDrift_energy_near f₀ A D hτ E)
    (finiteNoDrift_energy_shear f₀ A D hτ E)
    (finiteNoDrift_energy_forward f₀ A D hτ hδ hf₀ E)
    (finiteNoDrift_energy_anchor f₀ A D hτ hδ hf₀ E) (by simpa only [hj] using hc) hH
  rw [hj] at hbound
  have hw : f (FreeGroup.mk Double.obstructionWord) = H * (V * T⁻¹) * H⁻¹ * (V * T⁻¹)⁻¹ := by
    have he : Word.eval (fun g => f (FreeGroup.of g)) Double.obstructionWord =
        f (FreeGroup.mk Double.obstructionWord) := by rw [Word.eval, assignment_eq_lift]
    rw [← he]
    simp only [Double.obstructionWord, Word.eval_commutator, Word.eval_append, Word.eval_inverse, Word.eval_generator]
    rfl
  rw [hw]
  exact hbound

end ThomGame.Analysis
