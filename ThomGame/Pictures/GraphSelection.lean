module

public import ThomGame.Pictures.DiagramGraph
public import Mathlib.Data.List.OfFn

/-!
# Selecting whole graph components

A selection colors every vertex, with equal colors at the two ends of
each edge. Boundary words are filtered by position, not by generator label.
Selections restrict to both operands of diagram composition; the colors
on a vertical seam agree because its two ports share one vertex.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S}

/-- Keep selected occurrences in their original linear order. -/
def selectPositions (w : List S) (c : Fin w.length → Bool) : List S :=
  (List.ofFn fun i => if c i then some w[i] else none).filterMap id

@[simp] theorem selectPositions_nil (c : Fin 0 → Bool) :
    selectPositions ([] : List S) c = [] := rfl

theorem selectPositions_congr (w : List S) {c d : Fin w.length → Bool}
    (h : ∀ i, c i = d i) : selectPositions w c = selectPositions w d := by
  exact congrArg (selectPositions w) (funext h)

@[simp] theorem selectPositions_true (w : List S) :
    selectPositions w (fun _ => true) = w := by
  simp [selectPositions]

@[simp] theorem selectPositions_false (w : List S) :
    selectPositions w (fun _ => false) = [] := by
  simp [selectPositions, List.ofFn_const]

theorem selectPositions_const (w : List S) (b : Bool) :
    selectPositions w (fun _ => b) = if b then w else [] := by
  cases b <;> simp

theorem ofFn_appendIndex {A : Type*} (u v : List S) (f : Fin (u ++ v).length → A) :
    List.ofFn f = List.ofFn (fun i => f (appendIndex u v (.inl i))) ++
      List.ofFn (fun i => f (appendIndex u v (.inr i))) := by
  rw [List.ofFn_congr (List.length_append (as := u) (bs := v)), List.ofFn_add]
  rfl

theorem selectPositions_append (u v : List S) (c : Fin (u ++ v).length → Bool) :
    selectPositions (u ++ v) c =
      selectPositions u (fun i => c (appendIndex u v (.inl i))) ++
      selectPositions v (fun i => c (appendIndex u v (.inr i))) := by
  unfold selectPositions
  rw [ofFn_appendIndex u v, List.filterMap_append]
  simp only [get_appendIndex, Sum.elim_inl, Sum.elim_inr]

namespace PortGraph

variable {u v w z : List S}

structure Selection (G : PortGraph P u v) where
  pick : G.Vertex → Bool
  edge : ∀ a : G.Dart, pick (G.pairing.twin a).vertex = pick a.vertex

namespace Selection

variable {G : PortGraph P u v}

def top (c : G.Selection) (i : Fin u.length) : Bool := c.pick (.inl (.inl i))
def bottom (c : G.Selection) (i : Fin v.length) : Bool := c.pick (.inl (.inr i))
def hub (c : G.Selection) (h : G.Hub) : Bool := c.pick (.inr (.inl h))

end Selection

def compVertexLeft (G : PortGraph P u v) (H : PortGraph P v w) :
    G.Vertex → (G.comp H).Vertex
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr i) => .inr (.inr (.inr i))
  | .inr (.inl h) => .inr (.inl (.inl h))
  | .inr (.inr j) => .inr (.inr (.inl (.inl j)))

def compVertexRight (G : PortGraph P u v) (H : PortGraph P v w) :
    H.Vertex → (G.comp H).Vertex
  | .inl (.inl i) => .inr (.inr (.inr i))
  | .inl (.inr i) => .inl (.inr i)
  | .inr (.inl h) => .inr (.inl (.inr h))
  | .inr (.inr j) => .inr (.inr (.inl (.inr j)))

theorem compPorts_vertex_left (G : PortGraph P u v) (H : PortGraph P v w) (a : G.Dart) :
    (compPorts G H (.inl a)).vertex = compVertexLeft G H a.vertex := by cases a <;> rfl

theorem compPorts_vertex_right (G : PortGraph P u v) (H : PortGraph P v w) (a : H.Dart) :
    (compPorts G H (.inr a)).vertex = compVertexRight G H a.vertex := by cases a <;> rfl

def Selection.compLeft {G : PortGraph P u v} {H : PortGraph P v w}
    (c : (G.comp H).Selection) : G.Selection where
  pick x := c.pick (compVertexLeft G H x)
  edge a := by
    have h := c.edge (compPorts G H (.inl a))
    rw [twin_compPorts] at h
    exact (congrArg c.pick (compPorts_vertex_left G H (G.pairing.twin a))).symm.trans
      (h.trans (congrArg c.pick (compPorts_vertex_left G H a)))

def Selection.compRight {G : PortGraph P u v} {H : PortGraph P v w}
    (c : (G.comp H).Selection) : H.Selection where
  pick x := c.pick (compVertexRight G H x)
  edge a := by
    have h := c.edge (compPorts G H (.inr a))
    rw [twin_compPorts] at h
    exact (congrArg c.pick (compPorts_vertex_right G H (H.pairing.twin a))).symm.trans
      (h.trans (congrArg c.pick (compPorts_vertex_right G H a)))

theorem Selection.comp_seam {G : PortGraph P u v} {H : PortGraph P v w}
    (c : (G.comp H).Selection) : c.compLeft.bottom = c.compRight.top := rfl

def tensorVertexLeft (G : PortGraph P u v) (H : PortGraph P w z) :
    G.Vertex → (G.tensor H).Vertex
  | .inl (.inl i) => .inl (.inl (appendIndex u w (.inl i)))
  | .inl (.inr i) => .inl (.inr (appendIndex v z (.inl i)))
  | .inr (.inl h) => .inr (.inl (.inl h))
  | .inr (.inr j) => .inr (.inr (.inl j))

def tensorVertexRight (G : PortGraph P u v) (H : PortGraph P w z) :
    H.Vertex → (G.tensor H).Vertex
  | .inl (.inl i) => .inl (.inl (appendIndex u w (.inr i)))
  | .inl (.inr i) => .inl (.inr (appendIndex v z (.inr i)))
  | .inr (.inl h) => .inr (.inl (.inr h))
  | .inr (.inr j) => .inr (.inr (.inr j))

theorem tensorPorts_vertex_left (G : PortGraph P u v) (H : PortGraph P w z) (a : G.Dart) :
    (tensorPorts G H (.inl a)).vertex = tensorVertexLeft G H a.vertex := by cases a <;> rfl

theorem tensorPorts_vertex_right (G : PortGraph P u v) (H : PortGraph P w z) (a : H.Dart) :
    (tensorPorts G H (.inr a)).vertex = tensorVertexRight G H a.vertex := by cases a <;> rfl

def Selection.tensorLeft {G : PortGraph P u v} {H : PortGraph P w z}
    (c : (G.tensor H).Selection) : G.Selection where
  pick x := c.pick (tensorVertexLeft G H x)
  edge a := by
    have h := c.edge (tensorPorts G H (.inl a))
    rw [twin_tensorPorts] at h
    exact (congrArg c.pick (tensorPorts_vertex_left G H (G.pairing.twin a))).symm.trans
      (h.trans (congrArg c.pick (tensorPorts_vertex_left G H a)))

def Selection.tensorRight {G : PortGraph P u v} {H : PortGraph P w z}
    (c : (G.tensor H).Selection) : H.Selection where
  pick x := c.pick (tensorVertexRight G H x)
  edge a := by
    have h := c.edge (tensorPorts G H (.inr a))
    rw [twin_tensorPorts] at h
    exact (congrArg c.pick (tensorPorts_vertex_right G H (H.pairing.twin a))).symm.trans
      (h.trans (congrArg c.pick (tensorPorts_vertex_right G H a)))

end PortGraph
end ThomGame.Pictures
