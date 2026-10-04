module

public import ThomGame.Finite.InvolutionCyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Prefix parity around a cyclic word -/

@[expose] public section
namespace ThomGame

namespace CyclicParity

variable {α : Type*} [DecidableEq α]

def prefixParity (w : List α) (s : α) (k : Nat) : ZMod 2 := ((w.take k).count s : Nat)

theorem prefix_zero (w : List α) (s : α) : prefixParity w s 0 = 0 := by simp [prefixParity]

theorem prefix_length (w : List α) (s : α) : prefixParity w s w.length = (w.count s : ZMod 2) := by
  simp [prefixParity]

theorem prefix_succ (w : List α) (s : α) (k : Nat) (hk : k < w.length) :
    prefixParity w s (k + 1) = prefixParity w s k + if w[k] = s then 1 else 0 := by
  rw [prefixParity, List.take_succ_eq_append_getElem hk, List.count_append, Nat.cast_add]
  by_cases hs : w[k] = s <;> simp [prefixParity, hs]

theorem prefix_next (w : List α) (s : α) (he : Even (w.count s)) (j : Fin w.length) :
    prefixParity w s (finRotate w.length j).val =
      prefixParity w s j.val + if w[j.val] = s then 1 else 0 := by
  cases w with
  | nil => exact j.elim0
  | cons a w =>
    by_cases hj : j = Fin.last w.length
    · subst j
      have hs := prefix_succ (a :: w) s w.length (by simp)
      have ht : prefixParity (a :: w) s (w.length + 1) = 0 := by
        simpa [prefixParity] using he.natCast_zmod_two
      rw [ht] at hs
      simpa only [List.length_cons, finRotate_last, Fin.val_zero, Fin.val_last,
        prefix_zero] using hs
    · simp only [List.length_cons]
      rw [coe_finRotate_of_ne_last hj]
      exact prefix_succ (a :: w) s j.val j.isLt

end CyclicParity

namespace CyclicChain

variable {α : Type*} {R : α → α → Prop}

theorem get_next {w : List α} (h : CyclicChain R w) (j : Fin w.length) :
    R w[j.val] w[(finRotate w.length j).val] := by
  cases w with
  | nil => exact j.elim0
  | cons a w =>
    by_cases hj : j = Fin.last w.length
    · subst j
      have hm : (a :: w)[w.length] ∈ (a :: w).getLast? := by
        convert List.getLast_mem_getLast? (List.cons_ne_nil a w) using 1
        simp [List.getLast_eq_getElem]
      simpa only [List.length_cons, finRotate_last, Fin.val_zero, Fin.val_last,
        List.getElem_cons_zero] using h.2 _ hm a (by simp)
    · have hk : j.val + 1 < (a :: w).length := by
        have ht := Fin.val_lt_last hj
        simp only [List.length_cons]
        omega
      simpa only [List.length_cons, coe_finRotate_of_ne_last hj] using
        (List.isChain_iff_getElem.mp h.1) j.val hk

end CyclicChain
end ThomGame
