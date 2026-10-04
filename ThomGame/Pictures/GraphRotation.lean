module

public import ThomGame.Pictures.GraphEdges
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Local rotations and boundary circuits of port graphs

The ordered ports determine a cyclic rotation at each vertex. Composing
edge reversal with rotation gives the usual boundary-circuit permutation.
Its cycles are combinatorial circuits, not asserted to be geometric disk
faces. In particular, planarity and the treatment of disconnected regions
still require separate theorems.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

def hubRotation (h : G.Hub) : Equiv.Perm (Fin (P.word (G.hubLabel h)).length) :=
  if G.hubFlip h then (finRotate _).symm else finRotate _

theorem finRotate_sameCycle {n : Nat} (i j : Fin n) : (finRotate n).SameCycle i j := by
  let : NeZero n := i.neZero
  refine ⟨((j - i).val : Int), ?_⟩
  rw [zpow_natCast]
  change (finRotate n)^[(j - i).val] i = j
  rw [← finCycle_eq_finRotate_iterate]
  simp [finCycle_apply]

theorem hubRotation_sameCycle (h : G.Hub) (i j : Fin (P.word (G.hubLabel h)).length) :
    (G.hubRotation h).SameCycle i j := by
  unfold hubRotation
  split
  · exact (finRotate_sameCycle i j).inv
  · exact finRotate_sameCycle i j

/-- Boundary leaves are fixed, junction ports are exchanged, and hub ports
follow the defining word in the direction specified at that hub. -/
def rotation : Equiv.Perm G.Dart where
  toFun
    | .top i => .top i
    | .bottom i => .bottom i
    | .hub h i => .hub h (G.hubRotation h i)
    | .joint j side => .joint j (!side)
  invFun
    | .top i => .top i
    | .bottom i => .bottom i
    | .hub h i => .hub h ((G.hubRotation h).symm i)
    | .joint j side => .joint j (!side)
  left_inv a := by
    cases a with
    | top i => rfl
    | bottom i => rfl
    | hub h i => simp
    | joint j side => simp
  right_inv a := by
    cases a with
    | top i => rfl
    | bottom i => rfl
    | hub h i => simp
    | joint j side => simp

theorem vertex_rotation (a : G.Dart) : (G.rotation a).vertex = a.vertex := by
  cases a <;> rfl

theorem vertex_rotation_symm (a : G.Dart) : (G.rotation.symm a).vertex = a.vertex := by
  cases a <;> rfl

theorem rotation_hub (h : G.Hub) (i : Fin (P.word (G.hubLabel h)).length) :
    G.rotation (.hub h i) = .hub h (G.hubRotation h i) := rfl

theorem rotation_joint (j : G.Joint) (side : Bool) :
    G.rotation (.joint j side) = .joint j (!side) := rfl

theorem rotation_pow_hub (h : G.Hub) (n : Nat) (i : Fin (P.word (G.hubLabel h)).length) :
    (G.rotation ^ n) (.hub h i) = .hub h ((G.hubRotation h ^ n) i) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [pow_succ, Equiv.Perm.mul_apply, rotation_hub, ih]

theorem rotation_sameCycle_hub (h : G.Hub) (i j : Fin (P.word (G.hubLabel h)).length) :
    G.rotation.SameCycle (.hub h i) (.hub h j) := by
  obtain ⟨n, hn⟩ := (G.hubRotation_sameCycle h i j).exists_nat_pow_eq
  exact ⟨(n : Int), by rw [zpow_natCast, rotation_pow_hub, hn]⟩

theorem vertex_rotation_pow (n : Nat) (a : G.Dart) :
    ((G.rotation ^ n) a).vertex = a.vertex := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, vertex_rotation, ih]

/-- The rotation has exactly one orbit on the incident ports of each vertex. -/
theorem rotation_sameCycle_iff (a b : G.Dart) :
    G.rotation.SameCycle a b ↔ a.vertex = b.vertex := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [← hn, G.vertex_rotation_pow]
  · intro hab
    cases a with
    | top i =>
      cases b with
      | top j =>
        have hij : i = j := Sum.inl.inj (Sum.inl.inj hab)
        subst j
        exact Equiv.Perm.SameCycle.rfl
      | bottom j => cases hab
      | hub h j => cases hab
      | joint j side => cases hab
    | bottom i =>
      cases b with
      | top j => cases hab
      | bottom j =>
        have hij : i = j := Sum.inr.inj (Sum.inl.inj hab)
        subst j
        exact Equiv.Perm.SameCycle.rfl
      | hub h j => cases hab
      | joint j side => cases hab
    | hub h i =>
      cases b with
      | top j => cases hab
      | bottom j => cases hab
      | hub k j =>
        have hhk : h = k := Sum.inl.inj (Sum.inr.inj hab)
        subst k
        exact G.rotation_sameCycle_hub h i j
      | joint j side => cases hab
    | joint j side =>
      cases b with
      | top k => cases hab
      | bottom k => cases hab
      | hub h k => cases hab
      | joint k side' =>
        have hjk : j = k := Sum.inr.inj (Sum.inr.inj hab)
        subst k
        cases side <;> cases side'
        · exact Equiv.Perm.SameCycle.rfl
        · exact ⟨1, rfl⟩
        · exact ⟨1, rfl⟩
        · exact Equiv.Perm.SameCycle.rfl

def circuitStep : Equiv.Perm G.Dart := G.pairing.perm.trans G.rotation

theorem circuitStep_apply (a : G.Dart) :
    G.circuitStep a = G.rotation (G.pairing.twin a) := rfl

theorem circuitStep_symm_apply (a : G.Dart) :
    G.circuitStep.symm a = G.pairing.twin (G.rotation.symm a) := rfl

theorem vertex_circuitStep (a : G.Dart) :
    (G.circuitStep a).vertex = (G.pairing.twin a).vertex :=
  G.vertex_rotation (G.pairing.twin a)

theorem adj_circuitStep (a : G.Dart) : G.Adj a.vertex (G.circuitStep a).vertex :=
  ⟨a, rfl, (G.vertex_circuitStep a).symm⟩

def Circuit := Quotient (Equiv.Perm.SameCycle.setoid G.circuitStep)

instance : Finite G.Circuit := by
  unfold Circuit
  infer_instance

noncomputable instance : Fintype G.Circuit := Fintype.ofFinite _

def circuit (a : G.Dart) : G.Circuit := Quotient.mk _ a

theorem circuit_eq_iff (a b : G.Dart) :
    G.circuit a = G.circuit b ↔ G.circuitStep.SameCycle a b := Quotient.eq

theorem circuit_step (a : G.Dart) : G.circuit (G.circuitStep a) = G.circuit a := by
  apply (G.circuit_eq_iff _ _).mpr
  apply Equiv.Perm.SameCycle.symm
  exact ⟨1, by simp⟩

end ThomGame.Pictures.PortGraph
