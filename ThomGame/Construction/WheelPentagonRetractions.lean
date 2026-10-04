module

public import ThomGame.Construction.WheelPentagons
public import ThomGame.Finite.WheelPentagonFold
public import ThomGame.Finite.CyclicParity
public import Mathlib.Algebra.CharP.Two

/-!
# Retractions onto all actual five-sided wheel neighbourhoods

The phase is an explicit prefix count in each actual substituted word.
Every letter count is even, so the phase closes at the cyclic seam.
Adding the phase at the selected occurrence makes its own fold act as
the identity. Cyclic reduction supplies the required separation of hits.
-/

@[expose] public section
namespace ThomGame.Construction

theorem wheel_letters_ne_next (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    wheelFamily.letter r j ≠ wheelFamily.letter r (finRotate (wheelFamily.size r) j) :=
  (wheelWord_cyclicallyReduced r).get_next j

def wheelFoldPhase (s : Ordinary) (r₀ : WheelIndex) (j₀ : Fin (wheelFamily.size r₀)) :
    wheelFamily.FoldPhase s where
  value r j := CyclicParity.prefixParity (wheelWord r) s j.val +
    CyclicParity.prefixParity (wheelWord r₀) s j₀.val
  next r j := by
    change Fin (wheelWord r).length at j
    change CyclicParity.prefixParity (wheelWord r) s (finRotate (wheelWord r).length j).val +
        CyclicParity.prefixParity (wheelWord r₀) s j₀.val =
      (CyclicParity.prefixParity (wheelWord r) s j.val +
        CyclicParity.prefixParity (wheelWord r₀) s j₀.val) +
        if (wheelWord r)[j.val] = s then 1 else 0
    rw [CyclicParity.prefix_next (wheelWord r) s (wheelWord_count_even r s) j]
    exact add_right_comm _ _ _

theorem wheelFoldPhase_anchor (s : Ordinary) (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    (wheelFoldPhase s r j).value r j = 0 := CharTwo.add_self_eq_zero _

def pentagonWheelRetraction (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.Retraction system.hypergraph (Hypergraph.sun 5) :=
  wheelFamily.foldRetraction (wheelFamily.letter r j) (wheelFoldPhase (wheelFamily.letter r j) r j)
    wheel_letters_ne_next r j rfl (wheelFoldPhase_anchor _ r j)
    (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))

def numberedPentagonWheelRetraction (r : WheelIndex) (j : Fin (wheelFamily.size r)) :
    Hypergraph.Retraction numberedSystem.hypergraph (Hypergraph.sun 5) :=
  ((pentagonWheelRetraction r j).reindexSource rowEquiv colEquiv).congrSource
    (SparseSystem.hypergraph_reindex system rowEquiv colEquiv).symm

theorem first_row_rhs_zero_of_not_odd (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (h : (⟨r, j, 0⟩ : Row) ≠ oddRow) : system.rhs ⟨r, j, 0⟩ = 0 := by
  by_contra hn
  exact h ((rhs_ne_zero_iff _).mp hn)

def pentagonWheelStellar (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (h : (⟨r, j, 0⟩ : Row) ≠ oddRow) : (pentagonWheelCycle r j).Stellar system.rhs :=
  wheelFamily.foldStellar (wheelFamily.letter r j) (wheelFoldPhase (wheelFamily.letter r j) r j)
    wheel_letters_ne_next r j rfl (wheelFoldPhase_anchor _ r j)
    (Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))
    (first_row_rhs_zero_of_not_odd r j h)

def numberedPentagonWheelStellar (r : WheelIndex) (j : Fin (wheelFamily.size r))
    (h : (⟨r, j, 0⟩ : Row) ≠ oddRow) :
    (numberedPentagonWheelCycle r j).Stellar numberedSystem.rhs where
  retraction := numberedPentagonWheelRetraction r j
  vertex_eq _ := rfl
  rim_eq _ := rfl
  rhs_zero i := by
    have hv : (numberedPentagonWheelCycle r j).vertex i =
        rowEquiv ((pentagonWheelCycle r j).vertex i) := rfl
    rw [hv, numbered_rhs]
    exact (pentagonWheelStellar r j h).rhs_zero i

theorem oddPentagon_not_stellar :
    ¬ Nonempty ((pentagonWheelCycle none 0).Stellar system.rhs) := by
  rintro ⟨h⟩
  have hz := h.rhs_zero 0
  change (1 : ZMod 2) = 0 at hz
  exact one_ne_zero hz

end ThomGame.Construction
