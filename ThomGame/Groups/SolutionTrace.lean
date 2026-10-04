module

public import ThomGame.Groups.SolutionTriangle
public import ThomGame.Groups.InvolutionTrace

/-!
# Finite row-relation derivations for three-variable solution groups

Every relation occurrence is an actual matrix row. Commutation words are
unnecessary by the triangular-presentation equivalence. The character
counts the row occurrences modulo two, and its pairing with the right-hand
side is the exact change in central parity.
-/

@[expose] public section
namespace ThomGame.SolutionGroup

open scoped BigOperators
open InvolutionDerivation

variable {R C : Type*} (S : SparseSystem R C)

theorem word_eq_iff_trace (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ ms : List (Move R C), Valid (triangularPresentation S) ms (state w 0) (state [] a) := by
  rw [← InvolutionDerivation.word_eq_iff_trace]
  constructor
  · intro h
    have hh := congrArg (toTriangle S) h
    by_cases ha : a = 1 <;>
      simpa [map_list_prod, List.map_map, Function.comp_def, toTriangle_x, toTriangle_J, ha] using hh
  · intro h
    apply (triangularEquiv S).injective
    change toTriangle S ((w.map (x S)).prod) = toTriangle S (if a = 1 then J S else 1)
    by_cases ha : a = 1 <;>
      simpa [map_list_prod, List.map_map, Function.comp_def, toTriangle_x, toTriangle_J, ha] using h

theorem word_eq_iff_character_trace [Fintype R] [DecidableEq R] (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ ms : List (Move R C), Valid (triangularPresentation S) ms (state w 0) (state [] a) ∧
        ∑ r, character ms r * S.rhs r = a := by
  rw [word_eq_iff_trace]
  constructor
  · rintro ⟨ms, h⟩
    refine ⟨ms, h, ?_⟩
    have hh := valid_word_sign (triangularPresentation S) h
    rw [sign_eq_character] at hh
    exact hh
  · rintro ⟨ms, h, _⟩
    exact ⟨ms, h⟩

theorem J_eq_one_iff_closed_odd_trace [Fintype R] [DecidableEq R] :
    J S = 1 ↔ ∃ ms : List (Move R C),
      Valid (triangularPresentation S) ms (state [] 0) (state [] 1) ∧
        ∑ r, character ms r * S.rhs r = 1 := by
  simpa [eq_comm] using word_eq_iff_character_trace S [] 1

theorem word_eq_iff_checked_trace [DecidableEq C] (w : List C) (a : ZMod 2) :
    (w.map (x S)).prod = (if a = 1 then J S else 1) ↔
      ∃ ms : List (Move R C), check (triangularPresentation S) ms (state w 0) (state [] a) = true := by
  simp only [check_eq_true]
  exact word_eq_iff_trace S w a

end ThomGame.SolutionGroup
