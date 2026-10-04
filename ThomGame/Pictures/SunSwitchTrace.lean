module

public import ThomGame.Pictures.SunMinimalState

/-!
# Finite traces of actual sun switches

Every step is the explicit port-graph switch. Starting from a minimal
sun state, all intermediate graphs retain the boundary invariants and
minimum size, so every subsequent spoke satisfies the equal-orientation
hypothesis. The exact relation multiset and boundary quadrilateral paths
are retained along the trace. No termination or decrease of the number
of internal spokes is asserted here.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped BigOperators

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}

theorem SunSpoke.switch_boundary_spokes {G : PortGraph (sunPresentation n b) [] w}
    (s : G.SunSpoke)
    (hb : ∀ i : BoundaryIndex [] w, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j) :
    ∀ i : BoundaryIndex [] w, ∃ j, Port.label s.switch.jointLabel (s.switch.boundaryDart i) = Sum.inl j := by
  intro i
  cases i with
  | inl k => exact k.elim0
  | inr k => exact hb (.inr k)

inductive SunSwitchTrace : PortGraph (sunPresentation n b) [] w →
    PortGraph (sunPresentation n b) [] w → Type 1 where
  | refl (G) : SunSwitchTrace G G
  | step {G H} (s : G.SunSpoke) (tail : SunSwitchTrace s.switch H) : SunSwitchTrace G H

namespace SunSwitchTrace

variable {G H : PortGraph (sunPresentation n b) [] w} (t : SunSwitchTrace G H)

noncomputable def length {G H : PortGraph (sunPresentation n b) [] w} (t : SunSwitchTrace G H) : Nat := by
  induction t with
  | refl _ => exact 0
  | step _ _ ih => exact ih + 1

include t in
theorem minimalState (h : G.SunMinimalState) : H.SunMinimalState := by
  induction t with
  | refl _ => exact h
  | step s _ ih => exact ih (h.switch s)

include t in
theorem hub_card : Fintype.card H.Hub = Fintype.card G.Hub := by
  induction t with
  | refl _ => rfl
  | step _ _ ih => exact ih

include t in
theorem hub_relations : (∑ h : H.Hub, ([H.hubLabel h] : Multiset (Fin n))) =
    ∑ g : G.Hub, ([G.hubLabel g] : Multiset (Fin n)) := by
  induction t with
  | refl _ => rfl
  | step _ _ ih => exact ih

include t in
theorem boundaryNext (h : G.SunMinimalState) : H.boundaryNext = G.boundaryNext := by
  induction t with
  | refl _ => rfl
  | step s _ ih => exact (ih (h.switch s)).trans (s.switch_boundaryNext (h.same_flip s))

include t in
theorem exists_minimal_diagram (h : G.SunMinimalState) :
    ∃ d : Diagram (sunPresentation n b) [] w,
      (d.labels : Multiset (Fin n)) = (∑ x : G.Hub, ([G.hubLabel x] : Multiset (Fin n))) ∧
      d.size = Fintype.card G.Hub ∧ d.Minimal ∧ d.CharacterMinimal := by
  obtain ⟨d, hd, hn, _, hm, hc⟩ := (t.minimalState h).exists_minimal_diagram
  exact ⟨d, hd.trans t.hub_relations, hn.trans t.hub_card, hm, hc⟩

noncomputable def quadPath {G H : PortGraph (sunPresentation n b) [] w} (t : SunSwitchTrace G H)
    (hb : ∀ i : BoundaryIndex [] w, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)
    (q : G.BoundaryQuadPath) : H.BoundaryQuadPath := by
  induction t with
  | refl _ => exact q
  | step s _ ih => exact ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)

theorem quadPath_start
    (hb : ∀ i : BoundaryIndex [] w, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)
    (q : G.BoundaryQuadPath) : (t.quadPath hb q).start = q.start := by
  induction t with
  | refl _ => rfl
  | step s tail ih => exact ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)

theorem quadPath_finish
    (hb : ∀ i : BoundaryIndex [] w, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)
    (q : G.BoundaryQuadPath) : (t.quadPath hb q).finish = q.finish := by
  induction t with
  | refl _ => rfl
  | step s tail ih => exact ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)

end SunSwitchTrace
end ThomGame.Pictures.PortGraph
