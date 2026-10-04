module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Quot
public import Mathlib.Tactic.Choose

/-!
# A coherent minimum-weight representative in each finite equivalence class

Choosing on the quotient makes the representative constant on each
class, including when several elements have the same minimum weight.
-/

@[expose] public section
namespace ThomGame.Analysis

theorem exists_finite_class_minimum {μ : Type*} [Fintype μ]
    (r : μ → μ → Prop) (he : Equivalence r) (w : μ → Nat) :
    ∃ o : μ → μ, (∀ i, r i (o i)) ∧ (∀ i j, r i j → o i = o j) ∧
      (∀ i j, r i j → w (o i) ≤ w j) ∧ (∀ i, o (o i) = o i) := by
  classical
  let s : Setoid μ := ⟨r, he⟩
  have hchoose (q : Quotient s) : ∃ a : μ, Quotient.mk s a = q ∧
      ∀ b, Quotient.mk s b = q → w a ≤ w b := by
    let S := Finset.univ.filter (fun a => Quotient.mk s a = q)
    have hS : S.Nonempty := by
      refine ⟨q.out, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact q.out_eq
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S w hS
    refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
    intro b hb
    exact hmin b (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hb)
  choose f hf hmin using hchoose
  let o := fun i => f (Quotient.mk s i)
  have hrel i : r i (o i) := Quotient.exact (hf (Quotient.mk s i)).symm
  have hconst i j (hij : r i j) : o i = o j := congrArg f (Quotient.sound hij)
  refine ⟨o, hrel, hconst, ?_, ?_⟩
  · intro i j hij
    exact hmin (Quotient.mk s i) j (Quotient.sound (he.symm hij))
  · intro i
    exact (hconst i (o i) (hrel i)).symm

end ThomGame.Analysis
