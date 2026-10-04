module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Prod

/-!
# Consecutive numbering of variable-length blocks

`some i` labels ordinary blocks in their list order; `none` labels the last
block. The equivalence numbers each position by the sum of preceding lengths.
-/

@[expose] public section
namespace ThomGame.BlockNumbering

open scoped BigOperators

variable {n : Nat}

def prefixSum (s : Option (Fin n) → Nat) : Option (Fin n) → Nat
  | none => ∑ i, s (some i)
  | some i => ∑ k : Fin i.val, s (some (Fin.castLE i.isLt.le k))

/-- Separate the ordinary blocks from the distinguished final block. -/
def splitLast (s : Option (Fin n) → Nat) :
    (r : Option (Fin n)) × Fin (s r) ≃
      ((i : Fin n) × Fin (s (some i))) ⊕ Fin (s none) where
  toFun
    | ⟨none, j⟩ => .inr j
    | ⟨some i, j⟩ => .inl ⟨i, j⟩
  invFun
    | .inr j => ⟨none, j⟩
    | .inl ⟨i, j⟩ => ⟨some i, j⟩
  left_inv := by rintro ⟨r, j⟩; cases r <;> rfl
  right_inv := by intro p; cases p <;> rfl

theorem sum_split (s : Option (Fin n) → Nat) :
    (∑ i, s (some i)) + s none = ∑ r, s r := by
  rw [Fintype.sum_option, Nat.add_comm]

/-- A bijection with the consecutive zero-based position indices. -/
def positionEquiv (s : Option (Fin n) → Nat) :
    (r : Option (Fin n)) × Fin (s r) ≃ Fin (∑ r, s r) :=
  (((splitLast s).trans (finSigmaFinEquiv.sumCongr (Equiv.refl (Fin (s none))))).trans
    finSumFinEquiv).trans (finCongr (sum_split s))

theorem positionEquiv_val (s : Option (Fin n) → Nat)
    (r : Option (Fin n)) (j : Fin (s r)) :
    (positionEquiv s ⟨r, j⟩).val = prefixSum s r + j.val := by
  cases r with
  | none =>
    change (∑ i : Fin n, s (some i)) + j.val = (∑ i : Fin n, s (some i)) + j.val
    rfl
  | some i =>
    change (@finSigmaFinEquiv n (fun a => s (some a)) ⟨i, j⟩).val =
      (∑ k : Fin i.val, s (some (Fin.castLE i.isLt.le k))) + j.val
    exact finSigmaFinEquiv_apply (n := fun a => s (some a)) ⟨i, j⟩

/-- Change only the proved total, without evaluating the block data. -/
def positionEquivOfTotal (s : Option (Fin n) → Nat) (L : Nat) (h : (∑ r, s r) = L) :
    (r : Option (Fin n)) × Fin (s r) ≃ Fin L :=
  (positionEquiv s).trans (finCongr h)

theorem positionEquivOfTotal_val (s : Option (Fin n) → Nat) (L : Nat)
    (h : (∑ r, s r) = L) (r : Option (Fin n)) (j : Fin (s r)) :
    (positionEquivOfTotal s L h ⟨r, j⟩).val = prefixSum s r + j.val := by
  simp only [positionEquivOfTotal, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    positionEquiv_val]

/-- Number a fixed number of slots after each position. -/
def slotEquiv (s : Option (Fin n) → Nat) (L k : Nat) (h : (∑ r, s r) = L) :
    (r : Option (Fin n)) × (Fin (s r) × Fin k) ≃ Fin (L * k) :=
  ((Equiv.sigmaProdDistrib (fun r => Fin (s r)) (Fin k)).symm.trans
    ((positionEquivOfTotal s L h).prodCongr (Equiv.refl (Fin k)))).trans finProdFinEquiv

theorem slotEquiv_val (s : Option (Fin n) → Nat) (L k : Nat) (h : (∑ r, s r) = L)
    (r : Option (Fin n)) (j : Fin (s r)) (a : Fin k) :
    (slotEquiv s L k h ⟨r, j, a⟩).val = k * (prefixSum s r + j.val) + a.val := by
  change a.val + k * (positionEquivOfTotal s L h ⟨r, j⟩).val = _
  rw [positionEquivOfTotal_val]
  exact Nat.add_comm _ _

/-- A prefix sum over list indices equals the sum of the actual prefix. -/
theorem sum_get_take {α : Type*} (xs : List α) (f : α → Nat) (m : Nat) (hm : m ≤ xs.length) :
    (∑ i : Fin m, f (xs[i.val]'(lt_of_lt_of_le i.isLt hm))) = ((xs.take m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, List.take_succ_eq_append_getElem (by omega)]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    exact congrArg (fun a => a + f (xs[m]'(by omega))) (ih (by omega))

end ThomGame.BlockNumbering
