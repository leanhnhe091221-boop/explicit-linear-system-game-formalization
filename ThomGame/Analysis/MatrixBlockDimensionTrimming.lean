module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Sqrt

/-!
# Integer block trimming for dimension stability

A block of size r times s can be shortened on its larger factor, leaving
a deficit smaller than min(r,s). Retain whole blocks until the target
dimension is reached and shorten at most one block. The final deficit is
at most the integer square root of the original total dimension.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators

theorem exists_matrixBlock_trim (r s d : Nat) (hr : 0 < r) (hs : 0 < s)
    (hd : d < r * s) :
    ∃ r' s', r' ≤ r ∧ s' ≤ s ∧ r' * s' ≤ d ∧ d < r' * s' + min r s := by
  by_cases hsr : s ≤ r
  · refine ⟨d / s, s, ?_, le_rfl, Nat.div_mul_le_self d s, ?_⟩
    · have h := (Nat.div_lt_iff_lt_mul hs).mpr hd
      omega
    · rw [min_eq_right hsr]
      have hm := Nat.mod_lt d hs
      have he := Nat.mod_add_div d s
      rw [Nat.mul_comm s (d / s)] at he
      omega
  · have hrs : r ≤ s := by omega
    refine ⟨r, d / r, le_rfl, ?_, ?_, ?_⟩
    · have h := (Nat.div_lt_iff_lt_mul hr).mpr (by simpa only [Nat.mul_comm] using hd)
      omega
    · simpa only [Nat.mul_comm] using Nat.div_mul_le_self d r
    · rw [min_eq_left hrs]
      have hm := Nat.mod_lt d hr
      have he := Nat.mod_add_div d r
      omega

theorem exists_matrixBlocks_trim_bounded {n : Nat} (r s : Fin n → Nat) (d H : Nat)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (hH : ∀ i, min (r i) (s i) ≤ H)
    (hd : d ≤ ∑ i, r i * s i) :
    ∃ r' s' : Fin n → Nat,
      (∀ i, r' i ≤ r i) ∧ (∀ i, s' i ≤ s i) ∧
      (∑ i, r' i * s' i) ≤ d ∧ d ≤ (∑ i, r' i * s' i) + H := by
  induction n generalizing d with
  | zero =>
    have hd0 : d = 0 := by simpa using hd
    subst d
    exact ⟨r, s, fun _ => le_rfl, fun _ => le_rfl, by simp, by simp⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ] at hd
    by_cases hw : r 0 * s 0 ≤ d
    · have hd' : d - r 0 * s 0 ≤ ∑ i : Fin n, r i.succ * s i.succ := by omega
      obtain ⟨r', s', hrr, hss, hlow, hhigh⟩ := ih (fun i => r i.succ) (fun i => s i.succ)
        (d - r 0 * s 0) (fun i => hr i.succ) (fun i => hs i.succ) (fun i => hH i.succ) hd'
      refine ⟨Fin.cons (r 0) r', Fin.cons (s 0) s', ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases (by simp) (fun j => ?_) i
        simpa using hrr j
      · intro i
        refine Fin.cases (by simp) (fun j => ?_) i
        simpa using hss j
      · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
          (show r 0 * s 0 + (∑ i, r' i * s' i) ≤ d by omega)
      · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using
          (show d ≤ r 0 * s 0 + (∑ i, r' i * s' i) + H by omega)
    · obtain ⟨r₀, s₀, hrr, hss, hlow, hhigh⟩ := exists_matrixBlock_trim (r 0) (s 0) d (hr 0) (hs 0) (by omega)
      refine ⟨Fin.cons r₀ (fun _ => 0), Fin.cons s₀ (fun _ => 0), ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases (by simpa using hrr) (fun j => by simp) i
      · intro i
        refine Fin.cases (by simpa using hss) (fun j => by simp) i
      · simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero] using hlow
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero]
        have hh := hH 0
        omega

theorem matrixBlock_min_le_sqrt_total {n : Nat} (r s : Fin n → Nat) (i : Fin n) :
    min (r i) (s i) ≤ Nat.sqrt (∑ j, r j * s j) := by
  apply Nat.le_sqrt.mpr
  exact (Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)).trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (r j * s j)) (Finset.mem_univ i))

theorem exists_matrixBlocks_trim {n : Nat} (r s : Fin n → Nat) (d : Nat)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (hd : d ≤ ∑ i, r i * s i) :
    ∃ (r' s' : Fin n → Nat) (e : Nat),
      (∀ i, r' i ≤ r i) ∧ (∀ i, s' i ≤ s i) ∧
      (∑ i, r' i * s' i) + e = d ∧ e ≤ Nat.sqrt (∑ i, r i * s i) := by
  obtain ⟨r', s', hrr, hss, hlow, hhigh⟩ := exists_matrixBlocks_trim_bounded r s d
    (Nat.sqrt (∑ i, r i * s i)) hr hs (matrixBlock_min_le_sqrt_total r s) hd
  exact ⟨r', s', d - (∑ i, r' i * s' i), hrr, hss, by omega, by omega⟩

theorem exists_matrixBlocks_trim_relative {n : Nat} (r s : Fin n → Nat) (d : Nat)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (hd : d ≤ ∑ i, r i * s i) :
    ∃ (r' s' : Fin n → Nat) (e : Nat),
      (∀ i, r' i ≤ r i) ∧ (∀ i, s' i ≤ s i) ∧
      (∑ i, r' i * s' i) + e = d ∧ e ^ 2 ≤ ((∑ i, r i * s i) - d) * (∑ i, r i * s i) := by
  by_cases heq : d = ∑ i, r i * s i
  · exact ⟨r, s, 0, fun _ => le_rfl, fun _ => le_rfl, by omega, by simp⟩
  · obtain ⟨r', s', e, hrr, hss, he, heb⟩ := exists_matrixBlocks_trim r s d hr hs hd
    refine ⟨r', s', e, hrr, hss, he, ?_⟩
    have he2 : e ^ 2 ≤ ∑ i, r i * s i :=
      (Nat.pow_le_pow_left heb 2).trans (Nat.sqrt_le' _)
    have hgap : 1 ≤ (∑ i, r i * s i) - d := by omega
    exact he2.trans (by simpa using Nat.mul_le_mul_right (∑ i, r i * s i) hgap)

end ThomGame.Analysis
