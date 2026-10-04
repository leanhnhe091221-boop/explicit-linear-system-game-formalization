module

public import ThomGame.Analysis.FiniteNoDriftCertificate
public import ThomGame.Analysis.ApproxRepresentation
public import ThomGame.Groups.CompressorChecks
public import ThomGame.Groups.CompressorCompression
public import ThomGame.Groups.DoublePresentation

/-! Quantitative commutator estimates for the actual signed presentation words. -/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat}

noncomputable def finiteNoDriftComm (U : UnitaryMatrix d) (X : CMatrix d) : ℝ :=
  hsNorm (U.val * X - X * U.val)

theorem finiteNoDriftComm_nonneg (U : UnitaryMatrix d) (X : CMatrix d) : 0 ≤ finiteNoDriftComm U X :=
  hsNorm_nonneg _

theorem finiteNoDriftComm_inv (U : UnitaryMatrix d) (X : CMatrix d) :
    finiteNoDriftComm U⁻¹ X = finiteNoDriftComm U X := hsNorm_unitary_star_commutator U X

theorem finiteNoDriftComm_mul (U V : UnitaryMatrix d) (X : CMatrix d) :
    finiteNoDriftComm (U * V) X ≤ finiteNoDriftComm U X + finiteNoDriftComm V X := by
  have he : (U * V).val * X - X * (U * V).val =
      U.val * (V.val * X - X * V.val) + (U.val * X - X * U.val) * V.val := by
    change U.val * V.val * X - X * (U.val * V.val) = _
    noncomm_ring
  unfold finiteNoDriftComm
  rw [he]
  have ht := hsNorm_add_le (U.val * (V.val * X - X * V.val)) ((U.val * X - X * U.val) * V.val)
  rw [hsNorm_unitary_mul, hsNorm_mul_unitary] at ht
  linarith

theorem finiteNoDriftComm_conj (U V : UnitaryMatrix d) (X : CMatrix d) :
    finiteNoDriftComm (U * V * U⁻¹) X ≤ finiteNoDriftComm V X + 2 * finiteNoDriftComm U X := by
  have h₁ := finiteNoDriftComm_mul (U * V) U⁻¹ X
  have h₂ := finiteNoDriftComm_mul U V X
  rw [finiteNoDriftComm_inv] at h₁
  linarith

theorem finiteNoDriftComm_bracket (U V : UnitaryMatrix d) (X : CMatrix d) :
    finiteNoDriftComm (U * V * U⁻¹ * V⁻¹) X ≤ 2 * finiteNoDriftComm U X + 2 * finiteNoDriftComm V X := by
  have h₁ := finiteNoDriftComm_mul (U * V * U⁻¹) V⁻¹ X
  have h₂ := finiteNoDriftComm_conj U V X
  rw [finiteNoDriftComm_inv] at h₁
  linarith

theorem finiteNoDriftComm_close [NeZero d] (U V : UnitaryMatrix d) (X : CMatrix d)
    (hX : matrixOpNorm X ≤ 1) :
    finiteNoDriftComm U X ≤ finiteNoDriftComm V X + 2 * unitaryDist U V := by
  have hl := finiteNoDrift_commutator_unitary_lipschitz U V X hX
  rw [hsNorm_sub_comm (X * U.val), hsNorm_sub_comm (X * V.val)] at hl
  exact hl

theorem finiteNoDrift_eval_singleton {S G : Type*} [Group G] (f : S → G) (g : S) (b : Bool) :
    Word.eval f [(g, b)] = if b then f g else (f g)⁻¹ := by
  cases b
  · change Word.eval f (Word.inverse (Word.generator g)) = _
    simp
  · change Word.eval f (Word.generator g) = _
    simp

theorem finiteNoDrift_word_comm {S : Type*} (f : S → UnitaryMatrix d)
    (w : Word S) (X : CMatrix d) {a : ℝ}
    (hw : ∀ g b, (g, b) ∈ w → finiteNoDriftComm (f g) X ≤ a) :
    finiteNoDriftComm (Word.eval f w) X ≤ (w.length : ℝ) * a := by
  induction w with
  | nil => simp [finiteNoDriftComm]
  | cons p w ih =>
    have ih' := ih (fun g b h => hw g b (List.mem_cons_of_mem _ h))
    have hp : finiteNoDriftComm (Word.eval f [p]) X ≤ a := by
      rcases p with ⟨g, b⟩
      rw [finiteNoDrift_eval_singleton]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, finiteNoDriftComm_inv]
      all_goals exact hw g _ List.mem_cons_self
    have ht := finiteNoDriftComm_mul (Word.eval f [p]) (Word.eval f w) X
    rw [← Word.eval_append] at ht
    simp only [List.singleton_append] at ht
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem finiteNoDrift_equation_dist {S : Type*} (f : S → UnitaryMatrix d) (u v : Word S) {δ : ℝ}
    (h : unitaryLength (Word.eval f (Word.equation u v)) ≤ δ) :
    unitaryDist (Word.eval f u) (Word.eval f v) ≤ δ := by
  simpa only [Word.equation, Word.eval_append, Word.eval_inverse, unitaryDist_eq_length] using h

def FiniteNoDriftCompressorModel (f : Compressor.Generator → UnitaryMatrix d) (δ : ℝ) : Prop :=
  ∀ w ∈ Compressor.rawRelators, unitaryLength (Word.eval f w) ≤ δ

theorem finiteNoDrift_copy_model (f : MatrixAssignment Double.Generator d) {δ : ℝ}
    (hf : IsApproxRepresentation Double.relators δ f) (b : Bool) :
    FiniteNoDriftCompressorModel (fun g => f (FreeGroup.of (Double.copyGenerator b g))) δ := by
  intro w hw
  have hh := hf _ ⟨Double.copyWord b w, Double.copyWord_mem b w hw, rfl⟩
  have he : Word.eval (fun g => f (FreeGroup.of g)) (Double.copyWord b w) =
      f (FreeGroup.mk (Double.copyWord b w)) := by rw [Word.eval, assignment_eq_lift]
  rw [← he] at hh
  simpa only [Double.copyWord, Word.eval_map_generators] using hh

theorem finiteNoDrift_e2_dist (f : Compressor.Generator → UnitaryMatrix d) {δ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (r : Compressor.Root) (m : Compressor.Coeff) :
    unitaryDist
      (f (.inl (r, m)) * f (.inl (Compressor.right r, none)) *
        (f (.inl (r, m)))⁻¹ * (f (.inl (Compressor.right r, none)))⁻¹)
      (f (.inl (Compressor.across r, m))) ≤ δ := by
  have hmem : Word.equation (Word.commutator (Compressor.X r m) (Compressor.X (Compressor.right r) none))
      (Compressor.X (Compressor.across r) m) ∈ Compressor.e2e3 := by
    exact List.mem_flatMap.mpr ⟨r, Compressor.mem_roots r,
      List.mem_flatMap.mpr ⟨m, Compressor.mem_coefficients m, by simp⟩⟩
  have hm : Word.equation (Word.commutator (Compressor.X r m) (Compressor.X (Compressor.right r) none))
      (Compressor.X (Compressor.across r) m) ∈ Compressor.rawRelators := by
    simp only [Compressor.rawRelators, List.mem_append]
    tauto
  simpa only [Word.eval_commutator, Compressor.X, Word.eval_generator] using
    finiteNoDrift_equation_dist f _ _ (hf _ hm)

theorem finiteNoDrift_action_dist (f : Compressor.Generator → UnitaryMatrix d) {δ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (s r : Compressor.Root) (m : Compressor.Coeff) :
    unitaryDist (f (.inr s) * f (.inl (r, m)) * (f (.inr s))⁻¹)
      (Word.eval f (Compressor.actionTarget s r true m)) ≤ δ := by
  have hmem : Word.equation (Compressor.conjugate (Compressor.signed (Compressor.shear s) true)
      (Compressor.X r m)) (Compressor.actionTarget s r true m) ∈ Compressor.actionRelations := by
    exact List.mem_flatMap.mpr ⟨s, Compressor.mem_roots s,
      List.mem_flatMap.mpr ⟨true, by simp,
        List.mem_flatMap.mpr ⟨r, Compressor.mem_roots r,
          List.mem_map.mpr ⟨m, Compressor.mem_coefficients m, rfl⟩⟩⟩⟩
  have hm : Word.equation (Compressor.conjugate (Compressor.signed (Compressor.shear s) true)
      (Compressor.X r m)) (Compressor.actionTarget s r true m) ∈ Compressor.rawRelators := by
    simp only [Compressor.rawRelators, List.mem_append]
    tauto
  simpa only [Compressor.conjugate, Compressor.signed, ↓reduceIte, Word.eval_append,
    Word.eval_inverse, Compressor.X, Compressor.shear, Word.eval_generator] using
    finiteNoDrift_equation_dist f _ _ (hf _ hm)

theorem finiteNoDrift_recovery_dist (f : Compressor.Generator → UnitaryMatrix d) {δ : ℝ}
    (hf : FiniteNoDriftCompressorModel f δ) (c : Compressor.Axis) (r : Compressor.Root) :
    unitaryDist (Word.eval f (Compressor.recoveryWord c) * f (.inl (r, some (c, true))) *
      (Word.eval f (Compressor.recoveryWord c))⁻¹) (f (.inl (r, some (c, false)))) ≤ δ := by
  have hmem : Word.equation (Compressor.conjugate (Compressor.recoveryWord c)
      (Compressor.X r (some (c, true)))) (Compressor.X r (some (c, false))) ∈ Compressor.negativeRecovery := by
    exact List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
      List.mem_map.mpr ⟨r, Compressor.mem_roots r, rfl⟩⟩
  have hm : Word.equation (Compressor.conjugate (Compressor.recoveryWord c)
      (Compressor.X r (some (c, true)))) (Compressor.X r (some (c, false))) ∈ Compressor.rawRelators := by
    simp only [Compressor.rawRelators, List.mem_append]
    tauto
  simpa only [Compressor.conjugate, Word.eval_append, Word.eval_inverse, Compressor.X,
    Word.eval_generator] using finiteNoDrift_equation_dist f _ _ (hf _ hm)

end ThomGame.Analysis
