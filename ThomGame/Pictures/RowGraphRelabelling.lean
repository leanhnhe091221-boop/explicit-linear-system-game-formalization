module

public import ThomGame.Finite.TrivalentRetained
public import ThomGame.Pictures.RowGraphEmbedding

/-!
# Relabelling every actual hub without deleting the port graph

Only the incidence equation at each used hub is required. Label maps may
identify different edges or relations. The three slots at each hub still
form a permutation, and its orientation correction preserves the entire
rotation graph, not merely the relation multiset of a diagram witness.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} (G : SolutionGroup.RowGraph A u v)

structure RowRelabelling (B : SparseSystem T U) where
  edge : S → U
  hub : G.Hub → T
  incidence : ∀ h, (A.hypergraph.incidence (G.hubLabel h)).map edge = B.hypergraph.incidence (hub h)

namespace RowRelabelling

variable {G} (m : G.RowRelabelling B)

noncomputable def slotEquiv (h : G.Hub) : Equiv.Perm (Fin 3) :=
  A.mappedSlotEquiv B m.edge (G.hubLabel h) (m.hub h) (m.incidence h)

theorem slotEquiv_label (h : G.Hub) (i : Fin 3) :
    B.column (m.hub h) (m.slotEquiv h i) = m.edge (A.column (G.hubLabel h) i) :=
  A.mappedSlotEquiv_label B m.edge _ _ (m.incidence h) i

theorem slotEquiv_turn (h : G.Hub) (b : Bool) (i : Fin 3) :
    triangleTurn (b ^^ triangleFlip (m.slotEquiv h)) (m.slotEquiv h i) =
      m.slotEquiv h (triangleTurn b i) := triangleFlip_turn _ b i

noncomputable def portsRaw : G.Dart ≃
    Port (SolutionGroup.triangularPresentation B) (u.map m.edge) (v.map m.edge)
      G.Hub G.Joint m.hub where
  toFun
    | .top i => .top (mapWordIndex m.edge u i)
    | .bottom i => .bottom (mapWordIndex m.edge v i)
    | .hub h i => .hub h (m.slotEquiv h i)
    | .joint j side => .joint j side
  invFun
    | .top i => .top ((mapWordIndex m.edge u).symm i)
    | .bottom i => .bottom ((mapWordIndex m.edge v).symm i)
    | .hub h i => .hub h ((m.slotEquiv h).symm i)
    | .joint j side => .joint j side
  left_inv a := by
    cases a with
    | top i => exact congrArg Port.top ((mapWordIndex m.edge u).symm_apply_apply i)
    | bottom i => exact congrArg Port.bottom ((mapWordIndex m.edge v).symm_apply_apply i)
    | joint j side => rfl
    | hub h i =>
      exact congrArg (fun j : Fin 3 => (.hub h j : G.Dart)) ((m.slotEquiv h).symm_apply_apply i)
  right_inv a := by
    cases a with
    | top i => exact congrArg Port.top ((mapWordIndex m.edge u).apply_symm_apply i)
    | bottom i => exact congrArg Port.bottom ((mapWordIndex m.edge v).apply_symm_apply i)
    | joint j side => rfl
    | hub h i =>
      exact congrArg (fun j : Fin 3 => (.hub h j :
        Port (SolutionGroup.triangularPresentation B) (u.map m.edge) (v.map m.edge)
          G.Hub G.Joint m.hub)) ((m.slotEquiv h).apply_symm_apply i)

theorem portsRaw_label (a : G.Dart) :
    Port.label (m.edge ∘ G.jointLabel) (m.portsRaw a) = m.edge (Port.label G.jointLabel a) := by
  cases a with
  | top i => exact get_mapWordIndex m.edge u i
  | bottom i => exact get_mapWordIndex m.edge v i
  | joint j side => rfl
  | hub h i =>
    have hB (j : Fin 3) :
        Port.label (m.edge ∘ G.jointLabel)
          (.hub h j : Port (SolutionGroup.triangularPresentation B)
            (u.map m.edge) (v.map m.edge) G.Hub G.Joint m.hub) = B.column (m.hub h) j := by
      fin_cases j <;> rfl
    exact (hB (m.slotEquiv h i)).trans ((m.slotEquiv_label h i).trans
      (congrArg m.edge (SolutionGroup.rowGraph_port_label A G h i)).symm)

noncomputable def graph : SolutionGroup.RowGraph B (u.map m.edge) (v.map m.edge) where
  Hub := G.Hub
  Joint := G.Joint
  hubLabel := m.hub
  hubFlip h := G.hubFlip h ^^ triangleFlip (m.slotEquiv h)
  jointLabel := m.edge ∘ G.jointLabel
  pairing := (G.pairing.mapLabel m.edge).transport m.portsRaw _ m.portsRaw_label

noncomputable def ports : G.Dart ≃ m.graph.Dart := m.portsRaw

theorem ports_label (a : G.Dart) :
    Port.label m.graph.jointLabel (m.ports a) = m.edge (Port.label G.jointLabel a) := m.portsRaw_label a

theorem ports_twin (a : G.Dart) :
    m.graph.pairing.twin (m.ports a) = m.ports (G.pairing.twin a) := by
  change m.portsRaw (G.pairing.twin (m.portsRaw.symm (m.portsRaw a))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem ports_rotation (a : G.Dart) :
    m.graph.rotation (m.ports a) = m.ports (G.rotation a) := by
  cases a with
  | top i => rfl
  | bottom i => rfl
  | joint j side => rfl
  | hub h i =>
    change (Port.hub h (triangleTurn (G.hubFlip h ^^ triangleFlip (m.slotEquiv h))
      (m.slotEquiv h i)) : m.graph.Dart) =
        (Port.hub h (m.slotEquiv h (triangleTurn (G.hubFlip h) i)) : m.graph.Dart)
    exact congrArg (fun j : Fin 3 => (.hub h j : m.graph.Dart)) (m.slotEquiv_turn h (G.hubFlip h) i)

theorem ports_circuitStep (a : G.Dart) :
    m.graph.circuitStep (m.ports a) = m.ports (G.circuitStep a) := by
  rw [circuitStep_apply, m.ports_twin, m.ports_rotation]
  rfl

theorem hub_card : Fintype.card m.graph.Hub = Fintype.card G.Hub := rfl

theorem sign : m.graph.sign = ∑ h : G.Hub, B.rhs (m.hub h) := rfl

theorem sign_zero (hz : ∀ h, B.rhs (m.hub h) = 0) : m.graph.sign = 0 := by
  rw [m.sign]
  exact Finset.sum_eq_zero (fun h _ => hz h)

theorem noJoints [IsEmpty G.Joint] : IsEmpty m.graph.Joint := inferInstanceAs (IsEmpty G.Joint)

end RowRelabelling
end ThomGame.Pictures.PortGraph
