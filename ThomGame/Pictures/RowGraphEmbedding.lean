module

public import ThomGame.Finite.TrivalentEmbedding
public import ThomGame.Pictures.SolutionGraph
public import ThomGame.Pictures.GraphRotation

/-!
# Open trivalent embeddings act on actual port graphs

Each original hub and joint is retained. Boundary occurrences keep their
positions; hub slots follow the uniquely determined column permutation.
The hub orientation is adjusted to make local rotation commute exactly.
Thus the resulting graph has a port bijection preserving both edge
pairing and face rotation, with labels mapped by the given open embedding.
-/

@[expose] public section
namespace ThomGame.Pictures

namespace Pairing

variable {A S U : Type*} {label : A → S}

def mapLabel (p : Pairing label) (f : S → U) : Pairing (f ∘ label) where
  twin := p.twin
  involutive := p.involutive
  ne_self := p.ne_self
  label_twin a := congrArg f (p.label_twin a)

end Pairing

def mapWordIndex {S U : Type*} (f : S → U) (w : List S) : Fin w.length ≃ Fin (w.map f).length :=
  finCongr (List.length_map (f := f) (as := w)).symm

theorem get_mapWordIndex {S U : Type*} (f : S → U) (w : List S) (i : Fin w.length) :
    (w.map f)[mapWordIndex f w i] = f (w[i]) := by simp [mapWordIndex]

namespace PortGraph

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  {u v : List S} (G : SolutionGroup.RowGraph A u v)
  (ι : A.hypergraph.OpenEmbedding B.hypergraph)

noncomputable def rowEmbeddingPortsRaw : G.Dart ≃
    Port (SolutionGroup.triangularPresentation B) (u.map ι.edge) (v.map ι.edge)
      G.Hub G.Joint (ι.vertex ∘ G.hubLabel) where
  toFun
    | .top i => .top (mapWordIndex ι.edge u i)
    | .bottom i => .bottom (mapWordIndex ι.edge v i)
    | .hub h i => .hub h (ι.slotEquiv (G.hubLabel h) i)
    | .joint j side => .joint j side
  invFun
    | .top i => .top ((mapWordIndex ι.edge u).symm i)
    | .bottom i => .bottom ((mapWordIndex ι.edge v).symm i)
    | .hub h i => .hub h ((ι.slotEquiv (G.hubLabel h)).symm i)
    | .joint j side => .joint j side
  left_inv a := by
    cases a with
    | top i => exact congrArg Port.top ((mapWordIndex ι.edge u).symm_apply_apply i)
    | bottom i => exact congrArg Port.bottom ((mapWordIndex ι.edge v).symm_apply_apply i)
    | joint j side => rfl
    | hub h i =>
      exact congrArg (fun j : Fin 3 => (.hub h j : G.Dart))
        ((ι.slotEquiv (G.hubLabel h)).symm_apply_apply i)
  right_inv a := by
    cases a with
    | top i => exact congrArg Port.top ((mapWordIndex ι.edge u).apply_symm_apply i)
    | bottom i => exact congrArg Port.bottom ((mapWordIndex ι.edge v).apply_symm_apply i)
    | joint j side => rfl
    | hub h i =>
      exact congrArg (fun j : Fin 3 => (.hub h j :
        Port (SolutionGroup.triangularPresentation B) (u.map ι.edge) (v.map ι.edge)
          G.Hub G.Joint (ι.vertex ∘ G.hubLabel)))
        ((ι.slotEquiv (G.hubLabel h)).apply_symm_apply i)

theorem rowEmbeddingPortsRaw_label (a : G.Dart) :
    Port.label (ι.edge ∘ G.jointLabel) (G.rowEmbeddingPortsRaw ι a) =
      ι.edge (Port.label G.jointLabel a) := by
  cases a with
  | top i => exact get_mapWordIndex ι.edge u i
  | bottom i => exact get_mapWordIndex ι.edge v i
  | joint j side => rfl
  | hub h i =>
    have hB (j : Fin 3) :
        Port.label (ι.edge ∘ G.jointLabel)
          (.hub h j : Port (SolutionGroup.triangularPresentation B)
            (u.map ι.edge) (v.map ι.edge) G.Hub G.Joint (ι.vertex ∘ G.hubLabel)) =
          B.column (ι.vertex (G.hubLabel h)) j := by fin_cases j <;> rfl
    exact (hB (ι.slotEquiv (G.hubLabel h) i)).trans
      ((ι.slotEquiv_label (G.hubLabel h) i).trans
        (congrArg ι.edge (SolutionGroup.rowGraph_port_label A G h i)).symm)

noncomputable def embedRows : SolutionGroup.RowGraph B (u.map ι.edge) (v.map ι.edge) where
  Hub := G.Hub
  Joint := G.Joint
  hubLabel := ι.vertex ∘ G.hubLabel
  hubFlip h := G.hubFlip h ^^ triangleFlip (ι.slotEquiv (G.hubLabel h))
  jointLabel := ι.edge ∘ G.jointLabel
  pairing := (G.pairing.mapLabel ι.edge).transport (G.rowEmbeddingPortsRaw ι) _
    (G.rowEmbeddingPortsRaw_label ι)

noncomputable def rowEmbeddingPorts : G.Dart ≃ (G.embedRows ι).Dart := G.rowEmbeddingPortsRaw ι

theorem rowEmbeddingPorts_label (a : G.Dart) :
    Port.label (G.embedRows ι).jointLabel (G.rowEmbeddingPorts ι a) =
      ι.edge (Port.label G.jointLabel a) := G.rowEmbeddingPortsRaw_label ι a

theorem rowEmbeddingPorts_twin (a : G.Dart) :
    (G.embedRows ι).pairing.twin (G.rowEmbeddingPorts ι a) =
      G.rowEmbeddingPorts ι (G.pairing.twin a) := by
  change G.rowEmbeddingPortsRaw ι (G.pairing.twin
    ((G.rowEmbeddingPortsRaw ι).symm (G.rowEmbeddingPortsRaw ι a))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem rowEmbeddingPorts_rotation (a : G.Dart) :
    (G.embedRows ι).rotation (G.rowEmbeddingPorts ι a) = G.rowEmbeddingPorts ι (G.rotation a) := by
  cases a with
  | top i => rfl
  | bottom i => rfl
  | joint j side => rfl
  | hub h i =>
    change (Port.hub h (triangleTurn (G.hubFlip h ^^ triangleFlip (ι.slotEquiv (G.hubLabel h)))
      (ι.slotEquiv (G.hubLabel h) i)) : (G.embedRows ι).Dart) =
        (Port.hub h (ι.slotEquiv (G.hubLabel h) (triangleTurn (G.hubFlip h) i)) : (G.embedRows ι).Dart)
    exact congrArg (fun j : Fin 3 => (.hub h j : (G.embedRows ι).Dart))
      (ι.slotEquiv_turn (G.hubLabel h) (G.hubFlip h) i)

theorem rowEmbeddingPorts_circuitStep (a : G.Dart) :
    (G.embedRows ι).circuitStep (G.rowEmbeddingPorts ι a) =
      G.rowEmbeddingPorts ι (G.circuitStep a) := by
  rw [circuitStep_apply, G.rowEmbeddingPorts_twin, G.rowEmbeddingPorts_rotation]
  rfl

theorem embedRows_hub_card : Fintype.card (G.embedRows ι).Hub = Fintype.card G.Hub := rfl

theorem embedRows_sign : (G.embedRows ι).sign = ∑ h : G.Hub, B.rhs (ι.vertex (G.hubLabel h)) := rfl

theorem embedRows_sign_zero (hz : ∀ r, B.rhs (ι.vertex r) = 0) : (G.embedRows ι).sign = 0 := by
  rw [G.embedRows_sign]
  exact Finset.sum_eq_zero (fun h _ => hz (G.hubLabel h))

end PortGraph
end ThomGame.Pictures
