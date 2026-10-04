module

public import ThomGame.Pictures.CircuitCopySwitch
public import ThomGame.Pictures.RowEdgeSwitchEuler

/-!
# A noncopy facial cover supplies an Euler-saturated switched graph

Both ends of the two selected edges are at distinct actual vertices,
by simplicity of the original circuit. This supplies the Euler proof
for either facial orientation, without assuming the new graph is planar.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v}

namespace RowEdgeSwitch

variable (s : G.RowEdgeSwitch) (C : G.SimpleCircuit)

theorem eulerDefect_of_facial_cuts {i k : Fin C.length} (hik : i ≠ k)
    (hi : s.first = C.dart i) (hk : s.second = C.dart k)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : ∃ side, C.BoundsFaceOrbit side) :
    eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0 := by
  obtain ⟨side, hside⟩ := hf
  cases side
  · exact s.eulerDefect_of_same_face hEuler
      (((hside _).mpr ⟨i, hi.symm⟩).trans ((hside _).mpr ⟨k, hk.symm⟩).symm)
  · apply s.eulerDefect_of_twin_face hEuler
    · intro hv
      rw [hi, hk] at hv
      exact hik ((finRotate C.length).injective (C.vertex_injective
        ((C.next_vertex i).trans (hv.trans (C.next_vertex k).symm))))
    · have ht (l : Fin C.length) :
          C.port (finRotate C.length l, true) = G.pairing.twin (C.dart l) := by
        change G.pairing.twin (C.dart ((finRotate C.length).symm (finRotate C.length l))) = _
        rw [Equiv.symm_apply_apply]
      exact ((hside _).mpr ⟨finRotate C.length i, (ht i).trans (congrArg G.pairing.twin hi).symm⟩).trans
        ((hside _).mpr ⟨finRotate C.length k, (ht k).trans (congrArg G.pairing.twin hk).symm⟩).symm

end RowEdgeSwitch

namespace SimpleCircuit

variable [DecidableEq R] [DecidableEq S] {G : SolutionGroup.RowGraph A [] []} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (γ : Hypergraph.Cycle A.hypergraph)
  (hl : ∀ i : Fin C.length, Port.label G.jointLabel (C.dart i) ∈ Set.range γ.edge)
  (hc : C.IsLabelCover)

include hl hc in
theorem exists_noncopy_euler_switch (hn : ¬ C.IsLabelCopy)
    (hEuler : eulerDefect G.pairing.perm G.circuitStep = 0)
    (hf : ∃ side, C.BoundsFaceOrbit side) (j : Fin γ.length) :
    ∃ s : G.RowEdgeSwitch,
      (∃ i k : Fin C.length, i ≠ k ∧ s.first = C.dart i ∧ s.second = C.dart k) ∧
      Port.label G.jointLabel s.first = γ.edge j ∧
      eulerDefect s.graph.pairing.perm s.graph.circuitStep = 0 := by
  obtain ⟨s, ⟨i, k, hik, hi, hk⟩, hlabel⟩ := C.exists_noncopy_switch γ hl hc hn j
  exact ⟨s, ⟨i, k, hik, hi, hk⟩, hlabel, s.eulerDefect_of_facial_cuts C hik hi hk hEuler hf⟩

end SimpleCircuit
end ThomGame.Pictures.PortGraph
