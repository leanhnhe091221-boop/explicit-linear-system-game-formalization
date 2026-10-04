module

public import ThomGame.Finite.HypergraphCycles
public import ThomGame.Finite.HypergraphMultiplicity

/-!
# The sparse system and the actual rim of a sun

For size at least three, the spoke and the two cyclic rim edges at each
vertex are distinct. The resulting sparse system has exactly the already
defined sun incidence data, and its rim is a closed hypergraph cycle.
-/

@[expose] public section
namespace ThomGame.Hypergraph

theorem sun_next_ne_self {n : Nat} (hn : 3 ≤ n) (j : Fin n) : finRotate n j ≠ j := by
  let _ : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  intro h
  have hz : (1 : Fin n) = 0 := add_left_cancel (h.trans (add_zero j).symm)
  have hv := congrArg Fin.val hz
  change 1 % n = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  exact Nat.one_ne_zero hv

def sunSystem (n : Nat) (hn : 3 ≤ n) (b : Fin n → ZMod 2) :
    SparseSystem (Fin n) (Fin n ⊕ Fin n) where
  column j := ![Sum.inl j, Sum.inr j, Sum.inr (finRotate n j)]
  column_injective j := by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · rfl
    · cases hpq
    · cases hpq
    · cases hpq
    · rfl
    · exact ((sun_next_ne_self hn j) (Sum.inr.inj hpq).symm).elim
    · cases hpq
    · exact ((sun_next_ne_self hn j) (Sum.inr.inj hpq)).elim
    · rfl
  rhs := b

theorem sunSystem_hypergraph (n : Nat) (hn : 3 ≤ n) (b : Fin n → ZMod 2) :
    (sunSystem n hn b).hypergraph = sun n := rfl

theorem sun_rim_incident {n : Nat} (j k : Fin n) :
    Sum.inr k ∈ (sun n).incidence j ↔ j = k ∨ j = (finRotate n).symm k := by
  simp only [sun, Multiset.mem_coe, List.mem_cons, List.not_mem_nil,
    Sum.inr.injEq, Sum.inr_ne_inl, false_or, or_false]
  rw [eq_comm (a := k) (b := j), eq_comm (a := k) (b := finRotate n j),
    ← Equiv.eq_symm_apply]

def sunCycle (n : Nat) (hn : 3 ≤ n) : Cycle (sun n) where
  length := n
  length_ge_three := hn
  vertex := Function.Embedding.refl _
  edge := ⟨Sum.inr, Sum.inr_injective⟩
  edge_multiplicity j k := by
    change (sunSystem n hn (fun _ => 0)).hypergraph.multiplicity j (.inr k) = _
    rw [SparseSystem.hypergraph_multiplicity_eq_ite]
    exact ite_cond_congr (propext (sun_rim_incident j k))

theorem sunCycle_edge_range {n : Nat} (hn : 3 ≤ n) :
    Set.range (sunCycle n hn).edge = Set.range (Sum.inr : Fin n → Fin n ⊕ Fin n) := rfl

end ThomGame.Hypergraph
