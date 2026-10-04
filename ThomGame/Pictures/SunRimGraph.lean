module

public import ThomGame.Finite.SunSystem
public import ThomGame.Pictures.SunCharacter
public import ThomGame.Pictures.CycleFrontier

/-!
# Actual rim circuits and internal spokes of sun graphs

The sun presentation is definitionally the triangular presentation of
its sparse system. Its rim restrictions therefore inherit the proved
simple-circuit construction, including graphs with subdivision joints.
An internal spoke between relation vertices joins distinct vertices
with the same label, as needed for the local sun surgeries.
-/

@[expose] public section
namespace ThomGame.Pictures

theorem sunPresentation_triangular (n : Nat) (hn : 3 ≤ n) (b : Fin n → ZMod 2) :
    sunPresentation n b = SolutionGroup.triangularPresentation (Hypergraph.sunSystem n hn b) := rfl

theorem sunBoundary_no_rim {n : Nat} (hn : 3 ≤ n) {w : List (Fin n ⊕ Fin n)}
    (hw : ∀ z ∈ w, ∃ j, z = Sum.inl j) :
    ∀ z ∈ w, z ∉ Set.range (Hypergraph.sunCycle n hn).edge := by
  intro z hz
  obtain ⟨j, rfl⟩ := hw z hz
  rintro ⟨k, hk⟩
  cases hk

namespace PortGraph

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v)

abbrev sunRowGraph (hn : 3 ≤ n) : SolutionGroup.RowGraph (Hypergraph.sunSystem n hn b) u v := G

abbrev SunRimDart (hn : 3 ≤ n) :=
  (G.sunRowGraph hn).RimDart (Hypergraph.sunCycle n hn)

def sunRimHubDart (hn : 3 ≤ n) (h : G.Hub) : G.SunRimDart hn :=
  ⟨.hub h (1 : Fin 3), ⟨G.hubLabel h, rfl⟩⟩

noncomputable def sunRimSimpleCircuit (hn : 3 ≤ n)
    (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
    (a : G.SunRimDart hn) : G.SimpleCircuit :=
  (G.sunRowGraph hn).rimSimpleCircuit (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a

theorem sunRimSimpleCircuit_frontier_spokes (hn : 3 ≤ n)
    (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
    (a : G.SunRimDart hn) (s : Bool) :
    ∀ z ∈ (G.sunRimSimpleCircuit hn hu hv a).frontierWord s, ∃ j, z = Sum.inl j := by
  intro z hz
  have hno := (G.sunRowGraph hn).rimSimpleCircuit_frontierWord_no_rim (Hypergraph.sunCycle n hn)
    (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a s z hz
  cases z with
  | inl j => exact ⟨j, rfl⟩
  | inr j => exact (hno ⟨j, rfl⟩).elim

theorem sun_hub_spoke_iff (h : G.Hub) (k : Fin 3) (j : Fin n) :
    Port.label G.jointLabel (.hub h k : G.Dart) = Sum.inl j ↔ G.hubLabel h = j ∧ k = 0 := by
  fin_cases k <;> simp [Port.label, sunPresentation]

theorem sun_spoke_hub_endpoints {h k : G.Hub} {p : Fin 3}
    (he : G.pairing.twin (.hub h (0 : Fin 3)) = .hub k p) :
    G.hubLabel k = G.hubLabel h ∧ p = 0 ∧ h ≠ k := by
  have hl := G.pairing.label_twin (.hub h (0 : Fin 3))
  rw [he] at hl
  change Port.label G.jointLabel (.hub k p : G.Dart) = Sum.inl (G.hubLabel h) at hl
  obtain ⟨hk, hp⟩ := (G.sun_hub_spoke_iff k p (G.hubLabel h)).mp hl
  refine ⟨hk, hp, ?_⟩
  intro hhk
  subst k
  subst p
  exact G.pairing.ne_self (.hub h (0 : Fin 3)) he

end PortGraph
end ThomGame.Pictures
