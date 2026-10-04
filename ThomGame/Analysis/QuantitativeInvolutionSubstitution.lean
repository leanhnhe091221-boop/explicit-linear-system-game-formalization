module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import ThomGame.Finite.InvolutionEvaluation
public import Mathlib.Tactic.Linarith

/-! Reversing a four-letter involution block costs at most four square defects.
This controls the syntactic substitution even for approximate involutions. -/

@[expose] public section
namespace ThomGame.Analysis

variable {d : ℕ}

theorem unitaryDist_mul_mul_le (U V U' V' : UnitaryMatrix d) :
    unitaryDist (U * V) (U' * V') ≤ unitaryDist U U' + unitaryDist V V' := by
  have h := unitaryDist_triangle (U * V) (U' * V) (U' * V')
  simpa only [unitaryDist_mul_right, unitaryDist_mul_left] using h

end ThomGame.Analysis

namespace ThomGame.InvolutionWords

open Analysis

variable {A : Type*} {d : ℕ} (f : Generator A → UnitaryMatrix d) {δ : ℝ}

theorem letterBlock_product_error (hδ : 0 ≤ δ)
    (hf : ∀ s, unitaryLength (f s * f s) ≤ δ) (a : A × Bool) :
    unitaryDist ((letterBlock a).map f).prod
      (if a.2 then generatorImage f a.1 else (generatorImage f a.1)⁻¹) ≤ 4 * δ := by
  have hi (s : Generator A) : unitaryDist (f s) ((f s)⁻¹) ≤ δ := by
    rw [unitaryDist_eq_length, inv_inv]
    exact hf s
  rcases a with ⟨g, positive⟩
  cases positive with
  | true => simpa [letterBlock, block_product] using (by linarith : (0 : ℝ) ≤ 4 * δ)
  | false =>
    have hpair := unitaryDist_mul_mul_le (f (g, true)) (f (g, false))
      (f (g, true))⁻¹ (f (g, false))⁻¹
    have hfour := unitaryDist_mul_mul_le
      (f (g, true) * f (g, false)) (f (g, true) * f (g, false))
      ((f (g, true))⁻¹ * (f (g, false))⁻¹) ((f (g, true))⁻¹ * (f (g, false))⁻¹)
    have h₀ := hi (g, false)
    have h₁ := hi (g, true)
    have hb : unitaryDist
        ((f (g, true) * f (g, false)) * (f (g, true) * f (g, false)))
        (((f (g, true))⁻¹ * (f (g, false))⁻¹) *
          ((f (g, true))⁻¹ * (f (g, false))⁻¹)) ≤ 4 * δ := by linarith
    simpa [letterBlock, block, pair, generatorImage, pow_two, mul_inv_rev, mul_assoc] using hb

theorem substitute_product_error (hδ : 0 ≤ δ)
    (hf : ∀ s, unitaryLength (f s * f s) ≤ δ) (w : Word A) :
    unitaryDist ((substitute w).map f).prod (Word.eval (generatorImage f) w) ≤
      (4 * w.length : ℕ) * δ := by
  induction w with
  | nil => simp [substitute]
  | cons a w ih =>
    have he : Word.eval (generatorImage f) [a] =
        if a.2 then generatorImage f a.1 else (generatorImage f a.1)⁻¹ := by
      cases a with | mk g positive => cases positive <;> simp [Word.eval, FreeGroup.lift_mk]
    change unitaryDist ((letterBlock a ++ substitute w).map f).prod
      (Word.eval (generatorImage f) ([a] ++ w)) ≤ _
    rw [List.map_append, List.prod_append, Word.eval_append, he]
    have h := unitaryDist_mul_mul_le ((letterBlock a).map f).prod ((substitute w).map f).prod
      (if a.2 then generatorImage f a.1 else (generatorImage f a.1)⁻¹)
      (Word.eval (generatorImage f) w)
    have hb := letterBlock_product_error f hδ hf a
    simp only [List.length_cons, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at ih ⊢
    linarith

end ThomGame.InvolutionWords
