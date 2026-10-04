module

public import ThomGame.Construction.WheelSharedCopySurgery

/-!
# Lemma 11.9 for the actual numbered wheel constellation

The shared-edge case is two actual row-graph reconnections. The first
splits the primary rim and joins two neighbouring copies, preserving
the total count and maximality. The second cuts a private edge in the
joined noncopy and increases the total count by one. Maximality then
forces every constellation rim, including every central rim, to be a
facial copy. The complete character and hub count are preserved.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

namespace SigmaMaximalRimState

variable (h : SigmaMaximalRimState H)

include h in
theorem shared_noncopy_double_surgery (i j : WheelCycleIndex) (hij : i ≠ j)
    (hshare : Hypergraph.ShareEdge numberedWheelCycles i j)
    (hp : Hypergraph.HasPrivateEdge numberedWheelCycles j)
    (a : H.RimDart (numberedWheelCycles i)) (hn : ¬ (closedSigmaRimCircuit H i a).IsLabelCopy) :
    ∃ (s : H.RowEdgeSwitch) (t : s.graph.RowEdgeSwitch),
      eulerDefect t.graph.pairing.perm t.graph.circuitStep = 0 ∧
      (∀ k : WheelCycleIndex, SigmaRimsFacialCovers t.graph k) ∧
      t.graph.character = H.character ∧ Fintype.card t.graph.Hub = Fintype.card H.Hub ∧
      t.graph.totalRimCount numberedWheelCycles = H.totalRimCount numberedWheelCycles + 1 := by
  obtain ⟨s, hs, hcount, b, hb⟩ := h.shared_noncopy_first_surgery i j hij hshare hp a hn
  obtain ⟨t, he, hf, ht⟩ := hs.private_noncopy_surgery j hp b hb
  exact ⟨s, t, he, hf, t.character.trans s.character, t.hub_card.trans s.hub_card,
    ht.trans (congrArg (fun n : Nat => n + 1) hcount)⟩

include h in
theorem all_facial_copies (i : WheelCycleIndex) : SigmaRimsFacialCopies H i := by
  rcases numbered_private_or_neighbour i with hp | ⟨j, hji, hshare, hp⟩
  · exact h.private_copies i hp
  · intro a
    refine ⟨(h.covers i a).1, ?_⟩
    by_contra hn
    obtain ⟨s, t, he, hf, hc, hsize, hcount⟩ :=
      h.shared_noncopy_double_surgery i j hji.symm hshare hp a hn
    have hm := h.maximal t.graph inferInstance he hc hsize hf
    omega

end SigmaMaximalRimState

theorem exists_all_facial_copies
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCovers H i) :
    ∃ K : SigmaGraph [] [], IsEmpty K.Joint ∧ SigmaMaximalRimState K ∧
      K.character = H.character ∧ K.sign = H.sign ∧ Fintype.card K.Hub = Fintype.card H.Hub ∧
      ∀ i : WheelCycleIndex, SigmaRimsFacialCopies K i := by
  obtain ⟨K, hJ, hK, hc, hs, hn⟩ := exists_maximal_rim_state he hf
  let : IsEmpty K.Joint := hJ
  exact ⟨K, hJ, hK, hc, hs, hn, hK.all_facial_copies⟩

theorem J_sigma_eq_one_iff_all_facial_copies :
    J_sigma = 1 ↔ ∃ H : SigmaGraph [] [], IsEmpty H.Joint ∧
      eulerDefect H.pairing.perm H.circuitStep = 0 ∧ H.sign = 1 ∧
      ∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i := by
  constructor
  · intro hj
    obtain ⟨H, hJ, hH, hs⟩ := J_sigma_eq_one_iff_maximal_rim_state.mp hj
    let : IsEmpty H.Joint := hJ
    exact ⟨H, hJ, hH.euler, hs, hH.all_facial_copies⟩
  · rintro ⟨H, hJ, he, hs, hf⟩
    exact J_sigma_eq_one_iff_all_facial_covers.mpr
      ⟨H, hJ, he, hs, fun i a => ⟨(hf i a).1, (hf i a).2.1⟩⟩

end ThomGame.Construction
