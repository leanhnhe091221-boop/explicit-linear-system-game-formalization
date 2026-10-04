module

public import ThomGame.Pictures.Diagram
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sigma

/-!
# Finite labelled graphs described by paired ports

Every edge is a pair of distinct darts. A boundary vertex has one port,
a subdivision vertex has two ports, and a relation vertex has the ordered
ports of its actual defining word. Loops and parallel edges are allowed.
No planarity or region-replacement assertion is part of this definition.
-/

@[expose] public section
namespace ThomGame.Pictures

variable {S : Type*}

/-- A label-preserving, fixed-point-free involution pairs the ends of edges. -/
structure Pairing {A : Type*} (label : A → S) where
  twin : A → A
  involutive : Function.Involutive twin
  ne_self : ∀ a, twin a ≠ a
  label_twin : ∀ a, label (twin a) = label a

namespace Pairing

variable {A B : Type*} {label : A → S} (p : Pairing label)

def perm : Equiv.Perm A :=
  ⟨p.twin, p.twin, p.involutive, p.involutive⟩

def transport (e : A ≃ B) (label' : B → S) (h : ∀ a, label' (e a) = label a) :
    Pairing label' where
  twin b := e (p.twin (e.symm b))
  involutive b := by simp only [Equiv.symm_apply_apply, p.involutive _, Equiv.apply_symm_apply]
  ne_self b := by
    intro hb
    have := congrArg e.symm hb
    simp only [Equiv.symm_apply_apply] at this
    exact p.ne_self _ this
  label_twin b := by
    rw [h, p.label_twin, ← h, Equiv.apply_symm_apply]

def sum {label' : B → S} (q : Pairing label') : Pairing (Sum.elim label label') where
  twin := Sum.map p.twin q.twin
  involutive a := by
    cases a with
    | inl a => exact congrArg Sum.inl (p.involutive a)
    | inr b => exact congrArg Sum.inr (q.involutive b)
  ne_self a := by cases a <;> simp [Sum.map, p.ne_self, q.ne_self]
  label_twin a := by cases a <;> simp [Sum.map, p.label_twin, q.label_twin]

/-- The two darts of an edge, including when both are incident at one vertex. -/
def edgeSetoid : Setoid A where
  r a b := a = b ∨ a = p.twin b
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro a b (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, p.involutive])
    trans := by
      rintro a b c (hab | hab) (hbc | hbc)
      · exact Or.inl (hab.trans hbc)
      · exact Or.inr (hab.trans hbc)
      · exact Or.inr (by rw [hab, hbc])
      · exact Or.inl (by rw [hab, hbc, p.involutive]) }

def Edge := Quotient p.edgeSetoid

def edge (a : A) : p.Edge := Quotient.mk p.edgeSetoid a

theorem edge_eq_iff (a b : A) : p.edge a = p.edge b ↔ a = b ∨ a = p.twin b :=
  Quotient.eq

theorem edge_twin (a : A) : p.edge (p.twin a) = p.edge a :=
  (p.edge_eq_iff _ _).mpr (Or.inr rfl)

def edgeLabel : p.Edge → S := Quotient.lift label (by
  rintro a b (h | h)
  · rw [h]
  · rw [h, p.label_twin])

theorem edgeLabel_edge (a : A) : p.edgeLabel (p.edge a) = label a := rfl

end Pairing

variable {R : Type*} (P : InvolutionPresentation R S)

/-- Ports are indexed, so equal generator labels remain distinct occurrences. -/
inductive Port (u v : List S) (H J : Type) (hubLabel : H → R) : Type
  | top (i : Fin u.length)
  | bottom (i : Fin v.length)
  | hub (h : H) (i : Fin (P.word (hubLabel h)).length)
  | joint (j : J) (side : Bool)

namespace Port

variable {P} {u v : List S} {H J : Type} {hubLabel : H → R}

def sumEquiv :
    (Fin u.length ⊕ Fin v.length) ⊕
      ((Σ h : H, Fin (P.word (hubLabel h)).length) ⊕ (J × Bool)) ≃
        Port P u v H J hubLabel where
  toFun
    | .inl (.inl i) => .top i
    | .inl (.inr i) => .bottom i
    | .inr (.inl ⟨h, i⟩) => .hub h i
    | .inr (.inr (j, side)) => .joint j side
  invFun
    | .top i => .inl (.inl i)
    | .bottom i => .inl (.inr i)
    | .hub h i => .inr (.inl ⟨h, i⟩)
    | .joint j side => .inr (.inr (j, side))
  left_inv a := by rcases a with (i | i) | (⟨h, i⟩ | ⟨j, side⟩) <;> rfl
  right_inv a := by cases a <;> rfl

instance [Fintype H] [Fintype J] : Fintype (Port P u v H J hubLabel) :=
  Fintype.ofEquiv _ sumEquiv

def label (jointLabel : J → S) : Port P u v H J hubLabel → S
  | .top i => u[i]
  | .bottom i => v[i]
  | .hub h i => (P.word (hubLabel h))[i]
  | .joint j _ => jointLabel j

/-- Boundary vertices, relation vertices, and degree-two subdivision vertices. -/
abbrev Vertex (u v : List S) (H J : Type) := (Fin u.length ⊕ Fin v.length) ⊕ (H ⊕ J)

def vertex : Port P u v H J hubLabel → Vertex u v H J
  | .top i => .inl (.inl i)
  | .bottom i => .inl (.inr i)
  | .hub h _ => .inr (.inl h)
  | .joint j _ => .inr (.inr j)

/-- The complete ordered set of incidences at a vertex. -/
def Slots : Vertex u v H J → Type
  | .inl _ => Unit
  | .inr (.inl h) => Fin (P.word (hubLabel h)).length
  | .inr (.inr _) => Bool

def atVertex : (x : Vertex u v H J) → Slots (P := P) (hubLabel := hubLabel) x →
    Port P u v H J hubLabel
  | .inl (.inl i), _ => .top i
  | .inl (.inr i), _ => .bottom i
  | .inr (.inl h), i => .hub h i
  | .inr (.inr j), side => .joint j side

theorem vertex_at (x : Vertex u v H J) (i : Slots (P := P) (hubLabel := hubLabel) x) :
    (atVertex x i).vertex = x := by
  rcases x with (i | i) | (h | j) <;> rfl

def slot : (a : Port P u v H J hubLabel) → Slots (P := P) (hubLabel := hubLabel) a.vertex
  | .top _ => ()
  | .bottom _ => ()
  | .hub _ i => i
  | .joint _ side => side

theorem at_slot (a : Port P u v H J hubLabel) : atVertex a.vertex a.slot = a := by
  cases a <;> rfl

def incidentEquiv (x : Vertex u v H J) :
    Slots (P := P) (hubLabel := hubLabel) x ≃
      {a : Port P u v H J hubLabel // a.vertex = x} where
  toFun i := ⟨atVertex x i, vertex_at x i⟩
  invFun a := a.property ▸ a.val.slot
  left_inv i := by
    rcases x with (k | k) | (h | j) <;> cases i <;> rfl
  right_inv a := by
    rcases a with ⟨a, ha⟩
    subst x
    exact Subtype.ext (at_slot a)

instance slotsFintype (x : Vertex u v H J) :
    Fintype (Slots (P := P) (hubLabel := hubLabel) x) := by
  rcases x with (k | k) | (h | j) <;> dsimp [Slots] <;> infer_instance

end Port

/-- A finite graph with specified boundary and actual relation-port labels.
`hubFlip` records which direction reads the relation ports around a hub;
the combinatorial rotation and planarity theorems are developed separately. -/
structure PortGraph (u v : List S) where
  Hub : Type
  Joint : Type
  [hubFintype : Fintype Hub]
  [jointFintype : Fintype Joint]
  hubLabel : Hub → R
  hubFlip : Hub → Bool
  jointLabel : Joint → S
  pairing : Pairing (Port.label (P := P) (u := u) (v := v) (hubLabel := hubLabel) jointLabel)

attribute [instance] PortGraph.hubFintype PortGraph.jointFintype

namespace PortGraph

variable {P} {u v : List S} (G : PortGraph P u v)

abbrev Dart := Port P u v G.Hub G.Joint G.hubLabel
abbrev Vertex := Port.Vertex u v G.Hub G.Joint
abbrev Edge := G.pairing.Edge

noncomputable def degree (x : G.Vertex) : Nat := by
  classical
  exact Fintype.card {a : G.Dart // a.vertex = x}

theorem degree_top (i : Fin u.length) : G.degree (.inl (.inl i)) = 1 := by
  classical
  simpa [degree, Port.Slots] using
    (Fintype.card_congr (Port.incidentEquiv (P := P) (u := u) (v := v)
      (H := G.Hub) (J := G.Joint) (hubLabel := G.hubLabel) (.inl (.inl i)))).symm

theorem degree_bottom (i : Fin v.length) : G.degree (.inl (.inr i)) = 1 := by
  classical
  simpa [degree, Port.Slots] using
    (Fintype.card_congr (Port.incidentEquiv (P := P) (u := u) (v := v)
      (H := G.Hub) (J := G.Joint) (hubLabel := G.hubLabel) (.inl (.inr i)))).symm

theorem degree_hub (h : G.Hub) : G.degree (.inr (.inl h)) = (P.word (G.hubLabel h)).length := by
  classical
  simpa [degree, Port.Slots] using
    (Fintype.card_congr (Port.incidentEquiv (P := P) (u := u) (v := v)
      (H := G.Hub) (J := G.Joint) (hubLabel := G.hubLabel) (.inr (.inl h)))).symm

theorem degree_joint (j : G.Joint) : G.degree (.inr (.inr j)) = 2 := by
  classical
  simpa [degree, Port.Slots] using
    (Fintype.card_congr (Port.incidentEquiv (P := P) (u := u) (v := v)
      (H := G.Hub) (J := G.Joint) (hubLabel := G.hubLabel) (.inr (.inr j)))).symm

end PortGraph
end ThomGame.Pictures
