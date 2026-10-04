module

public import ThomGame.Construction.WheelPrivateCopies
public import ThomGame.Pictures.ConstellationSwitchFaces
public import ThomGame.Pictures.RowEdgeSwitchJoin
public import ThomGame.Finite.HypergraphConstellationStructure

/-!
# The first actual reconnection in Figure 18

The primary noncopy splits, while two different copied neighbouring
rims join into a noncopy. Every constellation rim remains a facial
cover, the total rim count stays fixed, and the output is therefore
another actual maximal state. The private-edge surgery can be applied
to that state to perform the second reconnection.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity
open scoped Classical

theorem numbered_private_or_neighbour (i : WheelCycleIndex) :
    Hypergraph.HasPrivateEdge numberedWheelCycles i ∨
      ∃ j, j ≠ i ∧ Hypergraph.ShareEdge numberedWheelCycles i j ∧
        Hypergraph.HasPrivateEdge numberedWheelCycles j := by
  rcases wheelConstellation.private_or_neighbour i with hp | ⟨j, hji, ⟨e, hei, hej⟩, hp⟩
  · exact Or.inl (numbered_hasPrivateEdge hp)
  · refine Or.inr ⟨j, hji, ⟨colEquiv e, ?_, ?_⟩, numbered_hasPrivateEdge hp⟩
    · apply (numberedWheelCycles_edge_range i _).mpr
      simpa only [Equiv.symm_apply_apply] using hei
    · apply (numberedWheelCycles_edge_range j _).mpr
      simpa only [Equiv.symm_apply_apply] using hej

theorem numbered_eq_or_eq_of_mem {i j k : WheelCycleIndex} (hij : i ≠ j) {e : Fin 1889684}
    (hei : e ∈ Set.range (numberedWheelCycles i).edge)
    (hej : e ∈ Set.range (numberedWheelCycles j).edge)
    (hek : e ∈ Set.range (numberedWheelCycles k).edge) : k = i ∨ k = j :=
  wheelConstellation.eq_or_eq_of_mem hij
    ((numberedWheelCycles_edge_range i e).mp hei)
    ((numberedWheelCycles_edge_range j e).mp hej)
    ((numberedWheelCycles_edge_range k e).mp hek)

variable {H : SigmaGraph [] []} [IsEmpty H.Joint]

theorem sigma_switch_faces_of_oriented_cuts
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCovers H i)
    (s : H.RowEdgeSwitch) (i : WheelCycleIndex)
    (ha : Port.label H.jointLabel s.first ∈ Set.range (numberedWheelCycles i).edge)
    (hsame : (H.rimWalk (numberedWheelCycles i) (numberedWheelCycles i).empty_boundary_no_rim (numberedWheelCycles i).empty_boundary_no_rim).SameCycle
      ⟨s.first, ha⟩ ⟨s.second, s.label_eq ▸ ha⟩) :
    ∀ m : WheelCycleIndex, SigmaRimsFacialCovers s.graph m := by
  intro m b
  exact ⟨s.all_rim_faces_of_oriented numberedWheelCycles numberedWheelCycles_intersection_unique
    (fun k x => (hf k x).1) i ha hsame m b,
    s.rim_covers (numberedWheelCycles m) (fun x => (hf m x).2) b⟩

namespace SigmaMaximalRimState

variable (h : SigmaMaximalRimState H)

omit [IsEmpty H.Joint] in
include h in
theorem switched_maximal (s : H.RowEdgeSwitch)
    (he : eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCovers s.graph i)
    (hn : s.graph.totalRimCount numberedWheelCycles = H.totalRimCount numberedWheelCycles) :
    SigmaMaximalRimState s.graph := by
  refine ⟨he, hf, ?_⟩
  intro K hJ hKe hKc hKs hKf
  rw [hn]
  exact h.maximal K hJ hKe (hKc.trans s.character) (hKs.trans s.hub_card) hKf

include h in
theorem shared_noncopy_first_surgery (i j : WheelCycleIndex) (hij : i ≠ j)
    (hshare : Hypergraph.ShareEdge numberedWheelCycles i j)
    (hp : Hypergraph.HasPrivateEdge numberedWheelCycles j)
    (a : H.RimDart (numberedWheelCycles i)) (hn : ¬ (closedSigmaRimCircuit H i a).IsLabelCopy) :
    ∃ s : H.RowEdgeSwitch, SigmaMaximalRimState s.graph ∧
      s.graph.totalRimCount numberedWheelCycles = H.totalRimCount numberedWheelCycles ∧
      ∃ b : s.graph.RimDart (numberedWheelCycles j), ¬ (closedSigmaRimCircuit s.graph j b).IsLabelCopy := by
  obtain ⟨e, ⟨l, hl⟩, hej⟩ := hshare
  obtain ⟨s, ⟨k, n, _, hk, hn'⟩, hlabel, he⟩ :=
    (closedSigmaRimCircuit H i a).exists_noncopy_euler_switch (numberedWheelCycles i)
      (H.rimSimpleCircuit_rim (numberedWheelCycles i) (numberedWheelCycles i).empty_boundary_no_rim (numberedWheelCycles i).empty_boundary_no_rim a)
      (h.covers i a).2 hn h.euler (h.covers i a).1 l
  have ha : Port.label H.jointLabel s.first ∈ Set.range (numberedWheelCycles i).edge :=
    ⟨l, hlabel.symm⟩
  have hb : Port.label H.jointLabel s.first ∈ Set.range (numberedWheelCycles j).edge :=
    (hlabel.trans hl).symm ▸ hej
  have hsep := rim_components_ne_of_copies (numberedWheelCycles j)
    (fun x => (h.private_copies j hp x).2) ⟨s.first, hb⟩ ⟨s.second, s.label_eq ▸ hb⟩
    s.different_edges s.label_eq
  have hsame := s.rimWalk_sameCycle_of_canonical_cuts (numberedWheelCycles i) a hk hn' ha
  have hf := sigma_switch_faces_of_oriented_cuts h.covers s i ha hsame
  have hother (m : WheelCycleIndex) (hmi : m ≠ i) (hmj : m ≠ j) :
      Port.label H.jointLabel s.first ∉ Set.range (numberedWheelCycles m).edge := by
    intro hm
    rcases numbered_eq_or_eq_of_mem hij ha hb hm with he | he
    · exact hmi he
    · exact hmj he
  have hcount := s.totalRimCount_split_join numberedWheelCycles i j hij
    (s.rimCount_split_of_canonical_cuts (numberedWheelCycles i) a hk hn')
    (s.rimCount_join (numberedWheelCycles j) hb hsep) hother
  exact ⟨s, h.switched_maximal s he hf hcount, hcount,
    ⟨s.first, hb⟩, s.joined_rim_not_copy (numberedWheelCycles j) hb hsep⟩

end SigmaMaximalRimState
end ThomGame.Construction
