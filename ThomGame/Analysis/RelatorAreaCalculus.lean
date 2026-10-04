module

public import ThomGame.Analysis.RelatorAreaBounds
public import Mathlib.Tactic.Group

/-! A bounded-area equality calculus for finite word certificates. -/

@[expose] public section
namespace ThomGame.Analysis

variable {G : Type*} [Group G] {rels : Set G}

def RelatorEquality (rels : Set G) (u v : G) (N : ℕ) : Prop :=
  ∃ n ≤ N, RelatorArea rels (u * v⁻¹) n

namespace RelatorEquality

variable {u v w a b : G} {M N : ℕ}

theorem of_eq (h : u = v) : RelatorEquality rels u v 0 := by
  subst v
  exact ⟨0, le_rfl, by simpa using (RelatorArea.one (rels := rels))⟩

theorem refl (u : G) : RelatorEquality rels u u 0 := of_eq rfl

theorem mono (h : RelatorEquality rels u v M) (hMN : M ≤ N) :
    RelatorEquality rels u v N := by
  obtain ⟨n, hn, hp⟩ := h
  exact ⟨n, hn.trans hMN, hp⟩

theorem symm (h : RelatorEquality rels u v N) : RelatorEquality rels v u N := by
  obtain ⟨n, hn, hp⟩ := h
  exact ⟨n, hn, hp.symm⟩

theorem trans (h₁ : RelatorEquality rels u v M) (h₂ : RelatorEquality rels v w N) :
    RelatorEquality rels u w (M + N) := by
  obtain ⟨m, hm, hp⟩ := h₁
  obtain ⟨n, hn, hq⟩ := h₂
  exact ⟨m+n, Nat.add_le_add hm hn, hp.trans hq⟩

theorem mul_right (h : RelatorEquality rels u v N) (w : G) :
    RelatorEquality rels (u*w) (v*w) N := by
  obtain ⟨n, hn, hp⟩ := h
  exact ⟨n, hn, hp.mul_right w⟩

theorem mul_left (h : RelatorEquality rels u v N) (w : G) :
    RelatorEquality rels (w*u) (w*v) N := by
  obtain ⟨n, hn, hp⟩ := h
  exact ⟨n, hn, hp.mul_left w⟩

theorem mul (h₁ : RelatorEquality rels u v M) (h₂ : RelatorEquality rels a b N) :
    RelatorEquality rels (u*a) (v*b) (M+N) :=
  (h₁.mul_right a).trans (h₂.mul_left v)

theorem inv (h : RelatorEquality rels u v N) :
    RelatorEquality rels u⁻¹ v⁻¹ N := by
  obtain ⟨n, hn, hp⟩ := h
  refine ⟨n, hn, ?_⟩
  have he : v⁻¹ * (v * u⁻¹) * (v⁻¹)⁻¹ = u⁻¹ * (v⁻¹)⁻¹ := by group
  rw [← he]
  exact hp.symm.conj v⁻¹

theorem commute_inv_left (h : RelatorEquality rels (u*v) (v*u) N) :
    RelatorEquality rels (u⁻¹*v) (v*u⁻¹) N := by
  have hh := ((h.mul_left u⁻¹).mul_right u⁻¹).symm
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh

theorem commute_inv_right (h : RelatorEquality rels (u*v) (v*u) N) :
    RelatorEquality rels (u*v⁻¹) (v⁻¹*u) N :=
  h.symm.commute_inv_left.symm

theorem unitaryDist_le {d : ℕ} (h : RelatorEquality rels u v N)
    (f : G →* UnitaryMatrix d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ r ∈ rels, unitaryLength (f r) ≤ δ) :
    unitaryDist (f u) (f v) ≤ (N : ℝ)*δ := by
  obtain ⟨n, hn, hp⟩ := h
  exact (hp.unitaryDist_le f δ hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hδ)

/-- Inverting the first root costs one central commutation. -/
theorem root_inv_left (h : RelatorEquality rels (u*v) (w*v*u) M)
    (huw : RelatorEquality rels (u*w) (w*u) N) :
    RelatorEquality rels (u⁻¹*v) (w⁻¹*v*u⁻¹) (M+N) := by
  have h₁ : RelatorEquality rels (v*u⁻¹) (u⁻¹*w*v) M := by
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using
      (h.mul_left u⁻¹).mul_right u⁻¹
  have h₂ : RelatorEquality rels (u⁻¹*w*v) (w*u⁻¹*v) N :=
    huw.commute_inv_left.mul_right v
  have hh := (h₁.trans h₂).mul_left w⁻¹
  simpa only [mul_assoc, inv_mul_cancel_left] using hh.symm

/-- Inverting the second root costs one central commutation. -/
theorem root_inv_right (h : RelatorEquality rels (u*v) (w*v*u) M)
    (hvw : RelatorEquality rels (v*w) (w*v) N) :
    RelatorEquality rels (u*v⁻¹) (w⁻¹*v⁻¹*u) (M+N) := by
  have h₁ : RelatorEquality rels (v⁻¹*u) (v⁻¹*w*v*u*v⁻¹) M := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using
      (h.mul_left v⁻¹).mul_right v⁻¹
  have h₂ : RelatorEquality rels (v⁻¹*w*v*u*v⁻¹) (w*u*v⁻¹) N := by
    have hh := ((hvw.commute_inv_left.mul_right v).mul_right u).mul_right v⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  have hh := (h₁.trans h₂).mul_left w⁻¹
  simpa only [mul_assoc, inv_mul_cancel_left] using hh.symm

end RelatorEquality
end ThomGame.Analysis
