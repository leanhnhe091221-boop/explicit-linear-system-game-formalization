module

public import ThomGame.Pictures.SunRimMembership
public import ThomGame.Pictures.RestrictedConnectivity

/-!
# A disjoint rim stays on one side of a cut rim

Every rim port at a vertex of a rim belongs to that rim component.
Consequently paths along another rim survive the cut. This includes
subdivision joints and does not require connectedness of the whole graph.
A side is propagated from an actual witnessing port, rather than chosen
for components that need not meet the cut rim's ambient component.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  (G : PortGraph (sunPresentation n b) u v) (hn : 3 ≤ n)
  (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)

theorem sunRimCircuit_onVertex_iff_connected (a x : G.SunRimDart hn) :
    (G.sunRimSimpleCircuit hn hu hv a).OnCircuitVertex x.val.vertex ↔
      Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a x := by
  constructor
  · intro hx
    exact (component_eq_iff _ _ _ _).mp
      ((G.sunRowGraph hn).rimSimpleCircuit_component_of_vertex (Hypergraph.sunCycle n hn)
        (sunBoundary_no_rim hn hu) (sunBoundary_no_rim hn hv) a x hx)
  · intro hx
    exact (G.sunRimSimpleCircuit hn hu hv a).marked_onCircuitVertex
      ((G.sunRimCircuit_marked_iff_connected hn hu hv a x).mpr hx)

theorem sunRimCircuit_cut_connected_of_rim_away (a x y : G.SunRimDart hn)
    (hax : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a x)
    (hxy : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm x y) :
    Connected G.circuitStep (G.sunRimSimpleCircuit hn hu hv a).cutPairing x.val y.val := by
  let C := G.sunRimSimpleCircuit hn hu hv a
  let p := (G.sunRimPairing hn).perm
  let q := (G.sunRimVertexPairing hn hu hv).perm
  let M := fun z => ¬ Connected p q a z
  have hp (z : G.SunRimDart hn) : M (p z) ↔ M z :=
    not_congr ⟨fun hz => hz.trans (Connected.edge z).symm,
      fun hz => hz.trans (Connected.edge z)⟩
  have hq (z : G.SunRimDart hn) : M (q z) ↔ M z :=
    not_congr ⟨fun hz => hz.trans (Connected.circuit z).symm,
      fun hz => hz.trans (Connected.circuit z)⟩
  have hy : M y := fun hay => hax (hay.trans hxy.symm)
  apply hxy.lift_restricted M hp hq hax hy (fun z => z.val.val)
    ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro z
    have hm : ¬ C.Marked z.val.val :=
      fun hm => z.property ((G.sunRimCircuit_marked_iff_connected hn hu hv a z.val).mp hm)
    change Connected G.circuitStep C.cutPairing z.val.val (G.pairing.twin z.val.val)
    rw [← C.cutPairing_of_unmarked z.val.val hm]
    exact Connected.circuit _
  · intro z
    apply C.cut_connected_same_vertex
    · exact fun hz => z.property ((G.sunRimCircuit_onVertex_iff_connected hn hu hv a z.val).mp hz)
    · exact ((G.sunRimVertexPairing hn hu hv).label_twin z.val).symm

theorem sunRimCircuit_onSide_iff_of_rim_away (a x y : G.SunRimDart hn)
    (hax : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a x)
    (hxy : Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm x y)
    (side : Bool) :
    (G.sunRimSimpleCircuit hn hu hv a).OnSide side x.val ↔
      (G.sunRimSimpleCircuit hn hu hv a).OnSide side y.val := by
  have h := G.sunRimCircuit_cut_connected_of_rim_away hn hu hv a x y hax hxy
  exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem sunRimCircuit_marked_onSide_of_rim_away (a x : G.SunRimDart hn)
    (hax : ¬ Connected (G.sunRimPairing hn).perm (G.sunRimVertexPairing hn hu hv).perm a x)
    (side : Bool) (hx : (G.sunRimSimpleCircuit hn hu hv a).OnSide side x.val)
    (y : G.Dart) (hy : (G.sunRimSimpleCircuit hn hu hv x).Marked y) :
    (G.sunRimSimpleCircuit hn hu hv a).OnSide side y := by
  let z : G.SunRimDart hn := ⟨y, G.sunRimCircuit_marked_rim hn hu hv x hy⟩
  have hz := (G.sunRimCircuit_marked_iff_connected hn hu hv x z).mp hy
  exact (G.sunRimCircuit_onSide_iff_of_rim_away hn hu hv a x z hax hz side).mp hx

end ThomGame.Pictures.PortGraph
