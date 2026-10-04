module

public import ThomGame.Pictures.PortGraph

/-! # The edges, incidences, and degree sum of a finite port graph -/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators

namespace Pairing

variable {A S : Type*} {label : A → S} (p : Pairing label)

instance [Finite A] : Finite p.Edge := by
  unfold Edge
  infer_instance

noncomputable instance [Fintype A] : Fintype p.Edge := Fintype.ofFinite _

noncomputable def edgeFiberEquiv (a : A) : Bool ≃ {b : A // p.edge b = p.edge a} := by
  classical
  exact {
    toFun := fun
      | false => ⟨a, rfl⟩
      | true => ⟨p.twin a, p.edge_twin a⟩
    invFun b := if b.val = a then false else true
    left_inv b := by cases b <;> simp [p.ne_self]
    right_inv b := by
      apply Subtype.ext
      rcases (p.edge_eq_iff _ _).mp b.property with h | h <;> simp [h, p.ne_self] }

theorem edge_fiber_nat_card (e : p.Edge) :
    Nat.card {a : A // p.edge a = e} = 2 := by
  refine Quotient.inductionOn e fun a => ?_
  calc
    Nat.card {b : A // p.edge b = p.edge a} = Nat.card Bool :=
      (Nat.card_congr (p.edgeFiberEquiv a)).symm
    _ = 2 := by simp

theorem edge_fiber_card [Fintype A] [DecidableEq p.Edge] (e : p.Edge) :
    Fintype.card {a : A // p.edge a = e} = 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact p.edge_fiber_nat_card e

theorem dart_card_eq_twice_edge_card [Fintype A] :
    Fintype.card A = 2 * Fintype.card p.Edge := by
  classical
  calc
    Fintype.card A = Fintype.card (Σ e : p.Edge, {a : A // p.edge a = e}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv p.edge)).symm
    _ = ∑ e : p.Edge, Fintype.card {a : A // p.edge a = e} := Fintype.card_sigma
    _ = ∑ _ : p.Edge, 2 := Finset.sum_congr rfl (fun e _ => p.edge_fiber_card e)
    _ = 2 * Fintype.card p.Edge := by simp [mul_comm]

end Pairing

namespace PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

/-- Adjacency retains a dart witness, so a loop contributes two incidences. -/
def Adj (x y : G.Vertex) : Prop :=
  ∃ a : G.Dart, a.vertex = x ∧ (G.pairing.twin a).vertex = y

theorem adj_symm {x y : G.Vertex} (h : G.Adj x y) : G.Adj y x := by
  rcases h with ⟨a, ha, hb⟩
  exact ⟨G.pairing.twin a, hb, by rw [G.pairing.involutive]; exact ha⟩

/-- Distinct port labels prevent an edge from joining a hub to itself. -/
theorem not_adj_self_hub (h : G.Hub)
    (hinj : Function.Injective (fun i : Fin (P.word (G.hubLabel h)).length =>
      (P.word (G.hubLabel h))[i])) : ¬ G.Adj (.inr (.inl h)) (.inr (.inl h)) := by
  rintro ⟨a, ha, hb⟩
  let e := Port.incidentEquiv (P := P) (u := u) (v := v) (H := G.Hub) (J := G.Joint)
    (hubLabel := G.hubLabel) (.inr (.inl h))
  obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
  obtain ⟨j, hj⟩ := e.surjective ⟨G.pairing.twin a, hb⟩
  have hi' : Port.hub h i = a := congrArg Subtype.val hi
  have hj' : Port.hub h j = G.pairing.twin a := congrArg Subtype.val hj
  have hlabels := G.pairing.label_twin a
  rw [← hj', ← hi'] at hlabels
  have hij : j = i := hinj hlabels
  exact G.pairing.ne_self a (by rw [← hj', hij, hi'])

def boundaryVertex : (Fin u.length ⊕ Fin v.length) ↪ G.Vertex :=
  ⟨Sum.inl, Sum.inl_injective⟩

def hubVertex : G.Hub ↪ G.Vertex :=
  ⟨fun h => .inr (.inl h), Sum.inr_injective.comp Sum.inl_injective⟩

def jointVertex : G.Joint ↪ G.Vertex :=
  ⟨fun j => .inr (.inr j), Sum.inr_injective.comp Sum.inr_injective⟩

theorem boundaryVertex_ne_hubVertex (i : Fin u.length ⊕ Fin v.length) (h : G.Hub) :
    G.boundaryVertex i ≠ G.hubVertex h := by simp [boundaryVertex, hubVertex]

theorem boundaryVertex_ne_jointVertex (i : Fin u.length ⊕ Fin v.length) (j : G.Joint) :
    G.boundaryVertex i ≠ G.jointVertex j := by simp [boundaryVertex, jointVertex]

theorem hubVertex_ne_jointVertex (h : G.Hub) (j : G.Joint) :
    G.hubVertex h ≠ G.jointVertex j := by simp [hubVertex, jointVertex]

/-- The port enumeration accounts for every incidence, including both ends of a loop. -/
theorem dart_card : Fintype.card G.Dart =
    u.length + v.length + ((∑ h : G.Hub, (P.word (G.hubLabel h)).length) +
      2 * Fintype.card G.Joint) := by
  calc
    Fintype.card G.Dart = Fintype.card
        ((Fin u.length ⊕ Fin v.length) ⊕
          ((Σ h : G.Hub, Fin (P.word (G.hubLabel h)).length) ⊕ (G.Joint × Bool))) :=
      (Fintype.card_congr Port.sumEquiv).symm
    _ = _ := by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma,
        Fintype.card_prod, Fintype.card_bool, mul_comm]

theorem degree_sum : u.length + v.length +
    ((∑ h : G.Hub, (P.word (G.hubLabel h)).length) + 2 * Fintype.card G.Joint) =
      2 * Fintype.card G.Edge := by
  rw [← G.dart_card]
  exact G.pairing.dart_card_eq_twice_edge_card

end PortGraph
end ThomGame.Pictures
