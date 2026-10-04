module

public import ThomGame.Pictures.CircuitCompositionFaces
public import ThomGame.Pictures.SelectedSmoothingTrace
public import ThomGame.Pictures.CircuitTrace

/-!
# Facial covers survive complete junction smoothing

A label cover uses only hub ports. Each of its original edges therefore
survives smoothing as one edge, rather than a longer wire. The resulting
simple circuit has exactly the original listed ports under the smoothing
embedding, retains its hub labels, and bounds the same exact face orbit.
The smoothing trace and its possibly nonempty circle records stay explicit.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} {circles : List S}

namespace Smoothing

variable (t : Smoothing G H circles)

theorem portEmbedding_vertex_iff (a b : H.Dart) :
    a.vertex = b.vertex ↔ (t.portEmbedding a).vertex = (t.portEmbedding b).vertex := by
  have ha : FiniteReturn.Advances G.rotation H.rotation t.portEmbedding :=
    fun x => Or.inl (t.portRotation x)
  exact (H.rotation_sameCycle_iff a b).symm.trans
    ((ha.sameCycle_iff a b).trans (G.rotation_sameCycle_iff _ _))

theorem portEmbedding_boundary_iff (a : H.Dart) :
    G.IsBoundary (t.portEmbedding a) ↔ H.IsBoundary a := by
  induction t with
  | refl _ => rfl
  | @step G H cs j tail ih =>
    exact (G.smooth_boundary_iff j (tail.portEmbedding a)).trans (ih a)

theorem portEmbedding_hub_data (h : H.Hub) (p : Fin (P.word (H.hubLabel h)).length) :
    ∃ (k : G.Hub) (q : Fin (P.word (G.hubLabel k)).length),
      t.portEmbedding (.hub h p) = .hub k q ∧ G.hubLabel k = H.hubLabel h := by
  induction t with
  | refl _ => exact ⟨h, p, rfl, rfl⟩
  | @step G H cs j tail ih =>
    obtain ⟨k, q, hk, hl⟩ := ih h p
    refine ⟨k, q, ?_, hl⟩
    change G.smoothPortEmbedding j (tail.portEmbedding (.hub h p)) = .hub k q
    rw [hk]
    rfl

variable [IsEmpty H.Joint]

theorem hub_data_of_portEmbedding {a : H.Dart} {h : G.Hub}
    {p : Fin (P.word (G.hubLabel h)).length} (he : t.portEmbedding a = .hub h p) :
    ∃ (k : H.Hub) (q : Fin (P.word (H.hubLabel k)).length),
      a = .hub k q ∧ H.hubLabel k = G.hubLabel h := by
  have hn : ¬ H.IsBoundary a := by
    intro hb
    have ho := (t.portEmbedding_boundary_iff a).mpr hb
    rw [he] at ho
    exact ho
  cases a with
  | top i => exact (hn trivial).elim
  | bottom i => exact (hn trivial).elim
  | joint j s => exact (isEmptyElim j : False).elim
  | hub k q =>
    obtain ⟨h', p', hh, hl⟩ := t.portEmbedding_hub_data k q
    have hv := congrArg Port.vertex (hh.symm.trans he)
    have hk : h' = h := by
      simpa only [Port.vertex, Sum.inr.injEq, Sum.inl.injEq] using hv
    exact ⟨k, q, rfl, hl.symm.trans (congrArg G.hubLabel hk)⟩

noncomputable def liftTerminal : {a : G.Dart // G.Terminal a} ≃ H.Dart := t.terminalEquiv.symm

theorem portEmbedding_liftTerminal (a : {a : G.Dart // G.Terminal a}) :
    t.portEmbedding (t.liftTerminal a) = a.val :=
  congrArg Subtype.val (t.terminalEquiv.apply_symm_apply a)

theorem twin_liftTerminal (a : G.Dart) (ha : G.Terminal a)
    (hb : G.Terminal (G.pairing.twin a)) :
    H.pairing.twin (t.liftTerminal ⟨a, ha⟩) = t.liftTerminal ⟨G.pairing.twin a, hb⟩ := by
  apply H.pairing.twin_eq_of_edge_eq
  · apply (t.wire_iff_final_edge _ _).mp
    rw [t.portEmbedding_liftTerminal, t.portEmbedding_liftTerminal]
    exact G.wireConnected_edge a
  · intro he
    have hx := congrArg t.portEmbedding he
    rw [t.portEmbedding_liftTerminal, t.portEmbedding_liftTerminal] at hx
    exact G.pairing.ne_self a hx.symm

end Smoothing

namespace PortGraph.SimpleCircuit

variable (C : G.SimpleCircuit) (hc : C.IsLabelCover)

include hc in
theorem cover_dart_terminal (i : Fin C.length) : G.Terminal (C.dart i) := by
  obtain ⟨h, k, p, q, he, ht, _, _⟩ := hc i
  rw [he]
  trivial

include hc in
theorem cover_twin_terminal (i : Fin C.length) : G.Terminal (G.pairing.twin (C.dart i)) := by
  obtain ⟨h, k, p, q, he, ht, _, _⟩ := hc i
  rw [ht]
  trivial

variable (t : Smoothing G H circles) [IsEmpty H.Joint]

noncomputable def reducedDart (i : Fin C.length) : H.Dart :=
  t.liftTerminal ⟨C.dart i, C.cover_dart_terminal hc i⟩

theorem portEmbedding_reducedDart (i : Fin C.length) :
    t.portEmbedding (C.reducedDart hc t i) = C.dart i := t.portEmbedding_liftTerminal _

theorem portEmbedding_twin_reducedDart (i : Fin C.length) :
    t.portEmbedding (H.pairing.twin (C.reducedDart hc t i)) = G.pairing.twin (C.dart i) := by
  rw [reducedDart, t.twin_liftTerminal _ _ (C.cover_twin_terminal hc i)]
  exact t.portEmbedding_liftTerminal _

/-- The original cover, with each hub port lifted into the fully smoothed graph. -/
@[reducible] noncomputable def reducedCover : H.SimpleCircuit where
  length := C.length
  length_pos := C.length_pos
  dart := ⟨C.reducedDart hc t, by
    intro i j he
    apply C.dart.injective
    have hh := congrArg t.portEmbedding he
    simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t] using hh⟩
  vertex_injective := by
    intro i j he
    apply C.vertex_injective
    have hh := (t.portEmbedding_vertex_iff _ _).mp he
    simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t] using hh
  edge_injective := by
    intro i j he
    apply C.edge_injective
    rcases (H.pairing.edge_eq_iff _ _).mp he with he | he
    · apply (G.pairing.edge_eq_iff _ _).mpr
      exact Or.inl (by simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t] using congrArg t.portEmbedding he)
    · apply (G.pairing.edge_eq_iff _ _).mpr
      exact Or.inr (by simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t,
        C.portEmbedding_twin_reducedDart hc t] using congrArg t.portEmbedding he)
  next_vertex := by
    intro i
    apply (t.portEmbedding_vertex_iff _ _).mpr
    simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t, C.portEmbedding_twin_reducedDart hc t] using
      C.next_vertex i
  next_ne_twin := by
    intro i he
    apply C.next_ne_twin i
    simpa only [Function.Embedding.coeFn_mk, C.portEmbedding_reducedDart hc t, C.portEmbedding_twin_reducedDart hc t] using
      congrArg t.portEmbedding he

theorem portEmbedding_reducedCover_port (x : Fin C.length × Bool) :
    t.portEmbedding ((C.reducedCover hc t).port x) = C.port x := by
  rcases x with ⟨i, side⟩
  cases side
  · exact C.portEmbedding_reducedDart hc t i
  · exact C.portEmbedding_twin_reducedDart hc t _

theorem reducedCover_isLabelCover : (C.reducedCover hc t).IsLabelCover := by
  intro i
  obtain ⟨h, k, p, q, hi, ht, _, hl⟩ := hc i
  obtain ⟨h', p', hh', hlabel⟩ := t.hub_data_of_portEmbedding
    ((C.portEmbedding_reducedDart hc t i).trans hi)
  obtain ⟨k', q', hk', klabel⟩ := t.hub_data_of_portEmbedding
    ((C.portEmbedding_twin_reducedDart hc t i).trans ht)
  have hne : H.hubLabel h' ≠ H.hubLabel k' := by
    rw [hlabel, klabel]
    exact hl
  exact ⟨h', k', p', q', hh', hk', fun he => hne (congrArg H.hubLabel he), hne⟩

theorem boundsFaceOrbit_reducedCover (side : Bool) (hf : C.BoundsFaceOrbit side) :
    (C.reducedCover hc t).BoundsFaceOrbit side := by
  intro x
  have hi : H.circuitStep.SameCycle x ((C.reducedCover hc t).port (0, side)) ↔
      G.circuitStep.SameCycle (t.portEmbedding x) (C.port (0, side)) := by
    rw [← H.circuit_eq_iff, t.sameCircuit_iff, G.circuit_eq_iff]
    rw [C.portEmbedding_reducedCover_port hc t (0, side)]
  rw [hi, hf]
  constructor
  · rintro ⟨i, he⟩
    exact ⟨i, t.portEmbedding.injective ((C.portEmbedding_reducedCover_port hc t (i, side)).trans he)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (C.portEmbedding_reducedCover_port hc t (i, side)).symm⟩

end PortGraph.SimpleCircuit
end ThomGame.Pictures
