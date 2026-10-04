module

public import ThomGame.Pictures.SunSwitchTrace

/-!
# Actual ports retained through a finite sun-switch trace

The trace retains the underlying ports and labels, their vertex
incidences, and every boundary position. Pairing may change at switched
hubs. On the three edges of each outer quadrilateral, both endpoints and
the exact quadrilateral certificate are retained throughout the trace.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSwitchTrace

variable {n : Nat} {b : Fin n → ZMod 2} {w : List (Fin n ⊕ Fin n)}
  {G H : PortGraph (sunPresentation n b) [] w}

noncomputable def ports (t : SunSwitchTrace G H) : G.Dart ≃ H.Dart := by
  induction t with
  | refl _ => exact Equiv.refl _
  | step _ _ ih => exact ih

variable (t : SunSwitchTrace G H)

theorem ports_label (x : G.Dart) : Port.label H.jointLabel (t.ports x) =
    Port.label G.jointLabel x := by
  induction t with
  | refl _ => rfl
  | step _ _ ih => exact ih x

theorem ports_vertex_iff (x y : G.Dart) :
    (t.ports x).vertex = (t.ports y).vertex ↔ x.vertex = y.vertex := by
  induction t with
  | refl _ => rfl
  | step _ _ ih => exact ih x y

theorem ports_boundaryDart (i : BoundaryIndex [] w) :
    t.ports (G.boundaryDart i) = H.boundaryDart i := by
  induction t with
  | refl _ => rfl
  | step s _ ih =>
    cases i with
    | inl k => exact k.elim0
    | inr k => exact ih

variable (hb : ∀ i : BoundaryIndex [] w, ∃ j, Port.label G.jointLabel (G.boundaryDart i) = Sum.inl j)
  (q : G.BoundaryQuadPath)

theorem quadPath_firstDart : (t.quadPath hb q).firstDart = t.ports q.firstDart := by
  induction t with
  | refl _ => rfl
  | @step G H s tail ih =>
    have he : (s.switchQuadPath q hb).firstDart = q.firstDart := by
      change s.switch.boundaryDart q.start = G.boundaryDart q.start
      cases q.start <;> rfl
    exact (ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)).trans (congrArg tail.ports he)

theorem quadPath_middleDart : (t.quadPath hb q).middleDart = t.ports q.middleDart := by
  induction t with
  | refl _ => rfl
  | step s _ ih => exact ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)

theorem quadPath_lastDart : (t.quadPath hb q).lastDart = t.ports q.lastDart := by
  induction t with
  | refl _ => rfl
  | step s _ ih => exact ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb)

include hb in
theorem quad_pairs_preserved : ∀ x ∈ [q.firstDart, q.middleDart, q.lastDart],
    H.pairing.twin (t.ports x) = t.ports (G.pairing.twin x) := by
  induction t with
  | refl _ => intro _ _; rfl
  | @step G H s tail ih =>
    intro x hx
    have he : (s.switchQuadPath q hb).firstDart = q.firstDart := by
      change s.switch.boundaryDart q.start = G.boundaryDart q.start
      cases q.start <;> rfl
    have hxi : x ∈ [(s.switchQuadPath q hb).firstDart,
        (s.switchQuadPath q hb).middleDart, (s.switchQuadPath q hb).lastDart] := by
      rw [he]
      exact hx
    have hp := ih (s.switch_boundary_spokes hb) (s.switchQuadPath q hb) x hxi
    rw [s.quad_pairs_preserved q hb x hx] at hp
    exact hp

end ThomGame.Pictures.PortGraph.SunSwitchTrace
