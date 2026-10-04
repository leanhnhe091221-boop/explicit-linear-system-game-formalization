module

public import ThomGame.Analysis.ApproxRepresentation

/-!
# Finite relator certificates and their quantitative error

`RelatorArea rels w n` records an actual derivation using `n` defining
relators, allowing inverses, conjugation and products.  Its matrix estimate
is dimension independent and does not use the qualitative approximation
transport theorem.  In particular a finite certificate can be checked
before it is evaluated at an approximate matrix representation.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {G : Type*} [Group G]

/-- A derivation of a word as a product of conjugates of defining relators. -/
inductive RelatorArea (rels : Set G) : G → ℕ → Prop
  | one : RelatorArea rels 1 0
  | relator {r : G} : r ∈ rels → RelatorArea rels r 1
  | inv {w : G} {n : ℕ} : RelatorArea rels w n → RelatorArea rels w⁻¹ n
  | mul {v w : G} {m n : ℕ} :
      RelatorArea rels v m → RelatorArea rels w n → RelatorArea rels (v * w) (m + n)
  | conj {w : G} {n : ℕ} (v : G) :
      RelatorArea rels w n → RelatorArea rels (v * w * v⁻¹) n

namespace RelatorArea

variable {rels : Set G} {w : G} {n : ℕ}

/-- Evaluate the finite proof in any unitary matrix dimension. -/
theorem unitaryLength_le {d : ℕ} (h : RelatorArea rels w n)
    (f : G →* UnitaryMatrix d) (δ : ℝ)
    (hδ : ∀ r ∈ rels, unitaryLength (f r) ≤ δ) :
    unitaryLength (f w) ≤ (n : ℝ) * δ := by
  induction h with
  | one => simp
  | relator hr => simpa using hδ _ hr
  | inv _ ih => simpa only [map_inv, unitaryLength_inv] using ih
  | mul _ _ ihv ihw =>
      rw [map_mul, Nat.cast_add, add_mul]
      exact (unitaryLength_mul_le _ _).trans (add_le_add ihv ihw)
  | conj v _ ih =>
      simpa only [map_mul, map_inv, unitaryLength_conj] using ih

theorem unitaryDist_le {d : ℕ} {v : G}
    (h : RelatorArea rels (w * v⁻¹) n) (f : G →* UnitaryMatrix d) (δ : ℝ)
    (hδ : ∀ r ∈ rels, unitaryLength (f r) ≤ δ) :
    unitaryDist (f w) (f v) ≤ (n : ℝ) * δ := by
  simpa only [map_mul, map_inv, ← unitaryDist_eq_length] using h.unitaryLength_le f δ hδ

/-- Concatenating two equality certificates adds their areas. -/
theorem trans {u v w : G} {m n : ℕ}
    (h₁ : RelatorArea rels (u * v⁻¹) m)
    (h₂ : RelatorArea rels (v * w⁻¹) n) :
    RelatorArea rels (u * w⁻¹) (m + n) := by
  simpa only [mul_assoc, inv_mul_cancel_left] using h₁.mul h₂

theorem symm {v w : G} {n : ℕ} (h : RelatorArea rels (v * w⁻¹) n) :
    RelatorArea rels (w * v⁻¹) n := by
  simpa only [mul_inv_rev, inv_inv] using h.inv

theorem mul_right {v w : G} {n : ℕ}
    (h : RelatorArea rels (v * w⁻¹) n) (u : G) :
    RelatorArea rels ((v * u) * (w * u)⁻¹) n := by
  simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h

theorem mul_left {v w : G} {n : ℕ}
    (h : RelatorArea rels (v * w⁻¹) n) (u : G) :
    RelatorArea rels ((u * v) * (u * w)⁻¹) n := by
  simpa only [mul_inv_rev, mul_assoc] using h.conj u

end RelatorArea

/-- Quantitative presentation transport from explicit relator certificates. -/
theorem isApproxRepresentation_comp_of_relatorArea
    {S T : Type*} {rels : Set (FreeGroup S)} {rels' : Set (FreeGroup T)}
    {d : ℕ} (f : MatrixAssignment T d) (φ : FreeGroup S →* FreeGroup T)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation rels' δ f)
    (N : ℕ) (hN : ∀ r ∈ rels, ∃ n ≤ N, RelatorArea rels' (φ r) n) :
    IsApproxRepresentation rels ((N : ℝ) * δ) (f.comp φ) := by
  intro r hr
  obtain ⟨n, hn, harea⟩ := hN r hr
  exact (harea.unitaryLength_le f δ hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hδ)

end ThomGame.Analysis
