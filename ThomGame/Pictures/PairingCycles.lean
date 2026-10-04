module

public import ThomGame.Pictures.GraphEdges
public import ThomGame.Pictures.RibbonConnectivity
public import Mathlib.Tactic.Group

/-!
# Oriented cycles in a finite graph with two ports at each vertex

The edge pairing and vertex pairing are fixed-point-free involutions.
Their alternating walk has two distinct orientations in each connected
component. Within one orientation neither an edge nor a vertex repeats.
Loops and parallel edges remain allowed in the underlying port graph.
-/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

variable {D E V : Type*} {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel)

def walk : Equiv.Perm D := p.perm.trans q.perm

theorem walk_apply (a : D) : walk p q a = q.twin (p.twin a) := rfl

theorem walk_edge (a : D) : walk p q (p.twin a) = q.twin a := by
  rw [walk_apply, p.involutive]

theorem walk_sandwich_edge : walk p q * p.perm * walk p q = p.perm := by
  ext a
  change q.twin (p.twin (p.twin (q.twin (p.twin a)))) = p.twin a
  rw [p.involutive, q.involutive]

theorem walk_sandwich_vertex : walk p q * q.perm * walk p q = q.perm := by
  ext a
  change q.twin (p.twin (q.twin (q.twin (p.twin a)))) = q.twin a
  rw [q.involutive, p.involutive]

theorem pow_sandwich (f r : Equiv.Perm D) (h : f * r * f = r) (n : Nat) :
    f ^ n * r * f ^ n = r := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      f ^ (n + 1) * r * f ^ (n + 1) = f ^ n * (f * r * f) * f ^ n := by group
      _ = r := by rw [h, ih]

theorem no_even_shift {L : Type*} {label : D → L} (r : Pairing label)
    (h : walk p q * r.perm * walk p q = r.perm) (n : Nat) (a : D) :
    (walk p q ^ (n + n)) a ≠ r.twin a := by
  intro he
  have hs := congrArg (fun f : Equiv.Perm D => f a) (pow_sandwich (walk p q) r.perm h n)
  change (walk p q ^ n) (r.twin ((walk p q ^ n) a)) = r.twin a at hs
  rw [pow_add, Equiv.Perm.mul_apply] at he
  exact r.ne_self _ ((walk p q ^ n).injective (hs.trans he.symm))

variable [Finite D]

theorem not_sameCycle_edge (a : D) : ¬ (walk p q).SameCycle a (p.twin a) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rcases Nat.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst k
    exact no_even_shift p q p (walk_sandwich_edge p q) n a hk
  · have hk' : (walk p q ^ (n + n + 1)) a = p.twin a := by
      have he : k = n + n + 1 := by omega
      simpa only [he] using hk
    have he : (walk p q ^ ((n + 1) + (n + 1))) a = q.twin a := by
      calc
        (walk p q ^ ((n + 1) + (n + 1))) a =
            walk p q ((walk p q ^ (n + n + 1)) a) := by
          rw [show (n + 1) + (n + 1) = (n + n + 1) + 1 by omega, pow_succ', Equiv.Perm.mul_apply]
        _ = walk p q (p.twin a) := by rw [hk']
        _ = q.twin a := walk_edge p q a
    exact no_even_shift p q q (walk_sandwich_vertex p q) (n + 1) a he

theorem not_sameCycle_vertex (a : D) : ¬ (walk p q).SameCycle a (q.twin a) := by
  intro h
  have hi := h.inv
  change (walk q p).SameCycle a (q.twin a) at hi
  exact not_sameCycle_edge q p a hi

theorem reverse_sameCycle {a b : D} (h : (walk p q).SameCycle a b) :
    (walk p q).SameCycle (p.twin a) (p.twin b) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  apply Equiv.Perm.SameCycle.symm
  refine ⟨(n : Int), ?_⟩
  rw [zpow_natCast]
  exact congrArg (fun f : Equiv.Perm D => f a)
    (pow_sandwich (walk p q) p.perm (walk_sandwich_edge p q) n)

theorem edge_injective_on_orbit {a x y : D}
    (hx : (walk p q).SameCycle a x) (hy : (walk p q).SameCycle a y)
    (he : p.edge x = p.edge y) : x = y := by
  rcases (p.edge_eq_iff x y).mp he with h | rfl
  · exact h
  · exact (not_sameCycle_edge p q y (hy.symm.trans hx)).elim

theorem vertex_injective_on_orbit {a x y : D}
    (hx : (walk p q).SameCycle a x) (hy : (walk p q).SameCycle a y)
    (he : q.edge x = q.edge y) : x = y := by
  rcases (q.edge_eq_iff x y).mp he with h | rfl
  · exact h
  · exact (not_sameCycle_vertex p q y (hy.symm.trans hx)).elim

def SameUnoriented (a b : D) : Prop :=
  (walk p q).SameCycle a b ∨ (walk p q).SameCycle (p.twin a) b

theorem sameUnoriented_equivalence : Equivalence (SameUnoriented p q) := by
  refine ⟨fun _ => Or.inl Equiv.Perm.SameCycle.rfl, ?_, ?_⟩
  · intro a b h
    rcases h with h | h
    · exact Or.inl h.symm
    · apply Or.inr
      have hr := reverse_sameCycle p q h
      rw [p.involutive] at hr
      exact hr.symm
  · intro a b c hab hbc
    rcases hab with hab | hab <;> rcases hbc with hbc | hbc
    · exact Or.inl (hab.trans hbc)
    · exact Or.inr ((reverse_sameCycle p q hab).trans hbc)
    · exact Or.inr (hab.trans hbc)
    · apply Or.inl
      have hr := reverse_sameCycle p q hab
      rw [p.involutive] at hr
      exact hr.trans hbc

theorem sameCycle_connected {a b : D} (h : (walk p q).SameCycle a b) :
    RibbonConnectivity.Connected p.perm q.perm a b := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, walk_apply]
    exact ih.trans ((RibbonConnectivity.Connected.edge _).trans (RibbonConnectivity.Connected.circuit _))

theorem connected_iff (a b : D) :
    RibbonConnectivity.Connected p.perm q.perm a b ↔ SameUnoriented p q a b := by
  constructor
  · intro h
    apply h.lift id (sameUnoriented_equivalence p q)
    · intro x
      exact Or.inr Equiv.Perm.SameCycle.rfl
    · intro x
      refine Or.inr ⟨1, ?_⟩
      change (walk p q ^ (1 : Int)) (p.twin x) = q.twin x
      rw [zpow_one]
      exact walk_edge p q x
  · rintro (h | h)
    · exact sameCycle_connected p q h
    · exact (RibbonConnectivity.Connected.edge a).trans (sameCycle_connected p q h)

end ThomGame.Pictures.PairingCycles
