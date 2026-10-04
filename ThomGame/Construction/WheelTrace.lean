module

public import ThomGame.Construction.SolutionGroup
public import ThomGame.Groups.SolutionTrace

/-!
# Rewrite certificates for the actual numbered solution group

The trace character pairs with b at only its unique nonzero row. Thus a
closed derivation of JΣ=1 must use that actual row an odd number of times.
This is an exact algebraic equivalence; ruling out such derivations still
requires the wheel picture argument.
-/

@[expose] public section
namespace ThomGame.Construction

open scoped BigOperators
open InvolutionDerivation

abbrev SigmaMove := Move (Fin 1417152) (Fin 1889684)

def sigmaTracePresentation := SolutionGroup.triangularPresentation numberedSystem

theorem numbered_rhs_pairing (c : Fin 1417152 → ZMod 2) :
    ∑ r, c r * numberedSystem.rhs r = c (rowEquiv oddRow) := by
  rw [Finset.sum_eq_single (rowEquiv oddRow)]
  · rw [b_odd, mul_one]
  · intro r _ hne
    have hz : numberedSystem.rhs r = 0 := by
      obtain ⟨s, rfl⟩ := rowEquiv.surjective r
      rw [numbered_rhs]
      by_contra h
      exact hne (congrArg rowEquiv ((rhs_ne_zero_iff s).mp h))
    rw [hz, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

theorem sigmaTrace_sign (ms : List SigmaMove) :
    sign sigmaTracePresentation ms = character ms (rowEquiv oddRow) := by
  rw [sign_eq_character]
  exact numbered_rhs_pairing (character ms)

theorem J_sigma_eq_one_iff_checked_odd_trace :
    J_sigma = 1 ↔ ∃ ms : List SigmaMove,
      check sigmaTracePresentation ms (state [] 0) (state [] 1) = true ∧
        character ms (rowEquiv oddRow) = 1 := by
  have hbase : J_sigma = 1 ↔ ∃ ms : List SigmaMove,
      check sigmaTracePresentation ms (state [] 0) (state [] 1) = true := by
    have h := SolutionGroup.word_eq_iff_checked_trace numberedSystem [] 1
    change (1 : SigmaGroup) = J_sigma ↔ ∃ ms : List SigmaMove,
      check sigmaTracePresentation ms (state [] 0) (state [] 1) = true at h
    exact eq_comm.trans h
  rw [hbase]
  constructor
  · rintro ⟨ms, h⟩
    refine ⟨ms, h, ?_⟩
    rw [← sigmaTrace_sign]
    exact valid_word_sign sigmaTracePresentation ((check_eq_true _ _ _ _).mp h)
  · rintro ⟨ms, h, _⟩
    exact ⟨ms, h⟩

theorem sigmaTrace_odd_row_number : (rowEquiv oddRow).val + 1 = 1417141 := by
  rw [rowEquiv_number, odd_row_number]

end ThomGame.Construction
