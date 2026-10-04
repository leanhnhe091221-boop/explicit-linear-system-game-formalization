module

public import ThomGame.Pictures.CycleSimpleCircuit
public import ThomGame.Pictures.CircuitFaceUniqueness

/-!
# Simple circuits with one hypergraph cycle's labels are its components

The two retained ports at each vertex force the continuation. Thus all
marked darts of a labelled simple circuit form exactly one restricted
rim component. Two such circuits sharing an edge have identical marked
ports, so an existing facial witness determines the whole component.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity

variable {R S : Type*} [DecidableEq R] [DecidableEq S] {A : SparseSystem R S}
  {u v : List S} {G : SolutionGroup.RowGraph A u v} (γ : Hypergraph.Cycle A.hypergraph)
  (hu : ∀ z ∈ u, z ∉ Set.range γ.edge) (hv : ∀ z ∈ v, z ∉ Set.range γ.edge)
  (C : G.SimpleCircuit)
  (hlabels : ∀ k : Fin C.length, Port.label G.jointLabel (C.dart k) ∈ Set.range γ.edge)

include hlabels in
theorem marked_label_rim {x : G.Dart} (hx : C.Marked x) : Port.label G.jointLabel x ∈ Set.range γ.edge := by
  obtain ⟨⟨k, side⟩, rfl⟩ := hx
  cases side
  · exact hlabels k
  · change Port.label G.jointLabel (G.pairing.twin (C.dart ((finRotate C.length).symm k))) ∈ _
    rw [G.pairing.label_twin]
    exact hlabels _

noncomputable def labelledRimDart (k : Fin C.length) : G.RimDart γ := ⟨C.dart k, hlabels k⟩

include hu hv hlabels in
theorem marked_of_rim_at_vertex (x : G.RimDart γ) (k : Fin C.length)
    (hx : x.val.vertex = (C.dart k).vertex) : C.Marked x.val := by
  classical
  let a : G.RimDart γ := C.labelledRimDart γ hlabels k
  let b : G.RimDart γ := ⟨C.incoming k,
    C.marked_label_rim γ hlabels ⟨(k, true), rfl⟩⟩
  have hab : b ≠ a := fun he => C.incoming_ne_outgoing k (congrArg Subtype.val he)
  have hb := G.rimSwitch_unique γ hu hv a b (C.incoming_vertex k) hab
  by_cases he : x = a
  · exact ⟨(k, false), congrArg Subtype.val he.symm⟩
  · have hxb := (G.rimSwitch_unique γ hu hv a x hx he).trans hb.symm
    exact ⟨(k, true), congrArg Subtype.val hxb.symm⟩

include hu hv in
theorem labelledRim_component (k : Fin C.length) :
    G.rimComponent γ hu hv (C.labelledRimDart γ hlabels k) =
      G.rimComponent γ hu hv (C.labelledRimDart γ hlabels 0) := by
  have hs (l : Fin C.length) :
      G.rimComponent γ hu hv (C.labelledRimDart γ hlabels (finRotate C.length l)) =
        G.rimComponent γ hu hv (C.labelledRimDart γ hlabels l) :=
    (G.rimComponent_vertex γ hu hv (C.next_vertex l)).trans
      (G.rimComponent_twin γ hu hv (C.labelledRimDart γ hlabels l))
  obtain ⟨m, hm⟩ := (finRotate_sameCycle (0 : Fin C.length) k).exists_nat_pow_eq
  rw [← hm]
  clear hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply, hs]
    exact ih

theorem marked_iff_rimComponent (x : G.RimDart γ) :
    C.Marked x.val ↔ G.rimComponent γ hu hv x =
      G.rimComponent γ hu hv (C.labelledRimDart γ hlabels 0) := by
  constructor
  · rintro ⟨⟨k, side⟩, he⟩
    exact (G.rimComponent_vertex γ hu hv
      ((congrArg Port.vertex he).symm.trans (C.port_vertex (k, side)))).trans
      (C.labelledRim_component γ hu hv hlabels k)
  · intro hx
    have hc := (component_eq_iff _ _ _ _).mp hx.symm
    let M (z : G.RimDart γ) : Prop := C.Marked z.val
    have hp (z : G.RimDart γ) (hz : M z) : M ((G.rimPairing γ).perm z) :=
      (C.marked_twin_iff z.val).mpr hz
    have hq (z : G.RimDart γ) (hz : M z) : M ((G.rimVertexPairing γ hu hv).perm z) := by
      obtain ⟨⟨k, side⟩, he⟩ := hz
      apply C.marked_of_rim_at_vertex γ hu hv hlabels _ k
      exact (G.rimSwitch_vertex γ hu hv z).trans
        ((congrArg Port.vertex he).symm.trans (C.port_vertex (k, side)))
    exact hc.predicate_of_forward M hp hq ⟨(0, false), rfl⟩

variable (D : G.SimpleCircuit)
  (hD : ∀ k : Fin D.length, Port.label G.jointLabel (D.dart k) ∈ Set.range γ.edge)

include hu hv hlabels hD in
theorem marked_iff_of_common_rim_port (x : G.Dart) (hC : C.Marked x) (hDx : D.Marked x) :
    ∀ y : G.Dart, C.Marked y ↔ D.Marked y := by
  let a : G.RimDart γ := ⟨x, C.marked_label_rim γ hlabels hC⟩
  have hc := (C.marked_iff_rimComponent γ hu hv hlabels a).mp hC
  have hd := (D.marked_iff_rimComponent γ hu hv hD a).mp hDx
  intro y
  constructor
  · intro hy
    let b : G.RimDart γ := ⟨y, C.marked_label_rim γ hlabels hy⟩
    exact (D.marked_iff_rimComponent γ hu hv hD b).mpr
      (((C.marked_iff_rimComponent γ hu hv hlabels b).mp hy).trans (hc.symm.trans hd))
  · intro hy
    let b : G.RimDart γ := ⟨y, D.marked_label_rim γ hD hy⟩
    exact (C.marked_iff_rimComponent γ hu hv hlabels b).mpr
      (((D.marked_iff_rimComponent γ hu hv hD b).mp hy).trans (hd.symm.trans hc))

include hu hv hlabels hD in
theorem exists_face_of_common_rim_port
    (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
      2 * Nat.card (Component G.circuitStep G.pairing.perm))
    (x : G.Dart) (hC : C.Marked x) (hDx : D.Marked x) (side : Bool) (hf : D.BoundsFaceOrbit side) :
    ∃ s, C.BoundsFaceOrbit s :=
  C.exists_face_of_marked_iff D (C.marked_iff_of_common_rim_port γ hu hv hlabels D hD x hC hDx)
    hEuler side hf

include hu hv hlabels hD in
theorem marked_iff_of_common_rim_edge (k : Fin C.length) (l : Fin D.length)
    (he : G.pairing.edge (C.dart k) = G.pairing.edge (D.dart l)) :
    ∀ y : G.Dart, C.Marked y ↔ D.Marked y := by
  have hd : D.Marked (C.dart k) := by
    rcases (G.pairing.edge_eq_iff _ _).mp he with he | he
    · exact he ▸ (show D.Marked (D.dart l) from ⟨(l, false), rfl⟩)
    · rw [he]
      exact (D.marked_twin_iff _).mpr ⟨(l, false), rfl⟩
  exact C.marked_iff_of_common_rim_port γ hu hv hlabels D hD (C.dart k) ⟨(k, false), rfl⟩ hd

end ThomGame.Pictures.PortGraph.SimpleCircuit
