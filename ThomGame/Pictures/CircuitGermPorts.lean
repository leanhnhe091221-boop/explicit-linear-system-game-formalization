module

public import ThomGame.Pictures.CircuitRegionPartition
public import ThomGame.Pictures.SelectedPorts

/-!
# Complete vertices and cut outward ports of a circuit germ

The germ keeps all circuit vertices and the selected interior vertices.
Its uncut edges are the circuit edges and that side's unmarked edges.
Every outward frontier port instead receives its own boundary copy,
even if the other end of its original edge is another circuit vertex.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} (C : G.SimpleCircuit)

def UncutDart (s : Bool) (a : G.Dart) : Prop := C.Marked a ∨ C.KeptDart s a

def GermVertex (s : Bool) (x : G.Vertex) : Prop := C.OnCircuitVertex x ∨ C.InteriorVertex s x

theorem uncutDart_twin_iff (s : Bool) (a : G.Dart) :
    C.UncutDart s (G.pairing.twin a) ↔ C.UncutDart s a := by
  unfold UncutDart
  rw [C.marked_twin_iff, C.keptDart_twin_iff]

noncomputable def uncutPairing (s : Bool) :
    Pairing (fun a : Subtype (C.UncutDart s) => Port.label G.jointLabel a.val) where
  twin a := ⟨G.pairing.twin a.val, (C.uncutDart_twin_iff s a.val).mpr a.property⟩
  involutive a := Subtype.ext (G.pairing.involutive a.val)
  ne_self a h := G.pairing.ne_self a.val (congrArg Subtype.val h)
  label_twin a := G.pairing.label_twin a.val

variable (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
  2 * Nat.card (Component G.circuitStep G.pairing.perm))

include hEuler in
theorem uncut_not_outward {s : Bool} {a : G.Dart} (ha : C.UncutDart s a) : ¬ C.Frontier (!s) a := by
  intro hf
  rcases ha with hm | ⟨_, hs⟩
  · exact hf.2 hm
  · have ht := ((C.frontier_iff hEuler (!s) a).mp hf).2.2
    exact (Bool.not_eq_self s).mp (C.onSide_unique hEuler hs ht).symm

include hEuler in
theorem germ_vertex_port_iff (s : Bool) (a : G.Dart) :
    C.GermVertex s a.vertex ↔ C.UncutDart s a ∨ C.Frontier (!s) a := by
  constructor
  · rintro (hv | hi)
    · by_cases hm : C.Marked a
      · exact Or.inl (Or.inl hm)
      · obtain ⟨t, ht⟩ := (C.exists_frontier_iff a).mpr ⟨hv, hm⟩
        by_cases he : t = s
        · subst t
          exact Or.inl (Or.inr ((C.frontier_iff hEuler s a).mp ht).2)
        · have hn : t = !s := by
            cases s <;> cases t <;> first | rfl | exact (he rfl).elim
          exact Or.inr (hn ▸ ht)
    · exact Or.inl (Or.inr (C.interior_port_kept s hi a rfl))
  · rintro ((hm | hk) | hf)
    · exact Or.inl (C.marked_onCircuitVertex hm)
    · by_cases hv : C.OnCircuitVertex a.vertex
      · exact Or.inl hv
      · exact Or.inr ⟨hv, a, rfl, hk.2⟩
    · exact Or.inl ((C.exists_frontier_iff a).mp ⟨!s, hf⟩).1

noncomputable def germOriginalEquiv (s : Bool) :
    {a : G.Dart // C.GermVertex s a.vertex} ≃
      Subtype (C.UncutDart s) ⊕ Subtype (C.Frontier (!s)) where
  toFun a := if ha : C.UncutDart s a.val then .inl ⟨a.val, ha⟩ else
    .inr ⟨a.val, ((C.germ_vertex_port_iff hEuler s a.val).mp a.property).resolve_left ha⟩
  invFun
    | .inl a => ⟨a.val, (C.germ_vertex_port_iff hEuler s a.val).mpr (Or.inl a.property)⟩
    | .inr a => ⟨a.val, (C.germ_vertex_port_iff hEuler s a.val).mpr (Or.inr a.property)⟩
  left_inv a := by by_cases ha : C.UncutDart s a.val <;> simp [ha]
  right_inv a := by
    rcases a with a | a
    · simp [a.property]
    · have hn : ¬ C.UncutDart s a.val := fun hu => C.uncut_not_outward hEuler hu a.property
      simp [hn]

include hEuler in
theorem germOriginalEquiv_val (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    Sum.elim Subtype.val Subtype.val (C.germOriginalEquiv hEuler s a) = a.val := by
  by_cases ha : C.UncutDart s a.val <;> simp [germOriginalEquiv, ha]

abbrev GermRaw (s : Bool) := Subtype (C.UncutDart s) ⊕ (Subtype (C.Frontier (!s)) × Bool)

def germRawLabel (s : Bool) : C.GermRaw s → S :=
  Sum.elim (fun a => Port.label G.jointLabel a.val) (fun a => Port.label G.jointLabel a.1.val)

noncomputable def germRawPairing (s : Bool) : Pairing (C.germRawLabel s) :=
  (C.uncutPairing s).sum (Pairing.copies (fun a : Subtype (C.Frontier (!s)) => Port.label G.jointLabel a.val))

def germReorder (s : Bool) :
    Subtype (C.Frontier (!s)) ⊕ (Subtype (C.UncutDart s) ⊕ Subtype (C.Frontier (!s))) ≃ C.GermRaw s where
  toFun
    | .inl a => .inr (a, true)
    | .inr (.inl a) => .inl a
    | .inr (.inr a) => .inr (a, false)
  invFun
    | .inl a => .inr (.inl a)
    | .inr (a, false) => .inr (.inr a)
    | .inr (a, true) => .inl a
  left_inv a := by rcases a with a | (a | a) <;> rfl
  right_inv a := by rcases a with a | ⟨a, b⟩; rfl; cases b <;> rfl

/-- The old port of a retained vertex, distinguished from its new boundary copy. -/
noncomputable def germOriginal (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) : C.GermRaw s :=
  C.germReorder s (.inr (C.germOriginalEquiv hEuler s a))

def germBoundary (s : Bool) (a : Subtype (C.Frontier (!s))) : C.GermRaw s := .inr (a, true)

include hEuler in
theorem germOriginal_label (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex}) :
    C.germRawLabel s (C.germOriginal hEuler s a) = Port.label G.jointLabel a.val := by
  have hv := C.germOriginalEquiv_val hEuler s a
  unfold germOriginal
  cases he : C.germOriginalEquiv hEuler s a with
  | inl b =>
    rw [he] at hv
    exact congrArg (Port.label G.jointLabel) hv
  | inr b =>
    rw [he] at hv
    exact congrArg (Port.label G.jointLabel) hv

include hEuler in
theorem germOriginal_of_uncut (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.UncutDart s a.val) : C.germOriginal hEuler s a = .inl ⟨a.val, ha⟩ := by
  simp [germOriginal, germOriginalEquiv, ha, germReorder]

include hEuler in
theorem germOriginal_of_outward (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.Frontier (!s) a.val) : C.germOriginal hEuler s a = .inr (⟨a.val, ha⟩, false) := by
  have hn : ¬ C.UncutDart s a.val := fun hu => C.uncut_not_outward hEuler hu ha
  simp [germOriginal, germOriginalEquiv, germReorder, hn]

include hEuler in
theorem germRaw_twin_original_uncut (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.UncutDart s a.val) :
    (C.germRawPairing s).twin (C.germOriginal hEuler s a) =
      C.germOriginal hEuler s ⟨G.pairing.twin a.val,
        (C.germ_vertex_port_iff hEuler s _).mpr (Or.inl ((C.uncutDart_twin_iff s _).mpr ha))⟩ := by
  rw [C.germOriginal_of_uncut hEuler s a ha,
    C.germOriginal_of_uncut hEuler s _ ((C.uncutDart_twin_iff s _).mpr ha)]
  rfl

include hEuler in
theorem germRaw_twin_original_outward (s : Bool) (a : {a : G.Dart // C.GermVertex s a.vertex})
    (ha : C.Frontier (!s) a.val) :
    (C.germRawPairing s).twin (C.germOriginal hEuler s a) = C.germBoundary s ⟨a.val, ha⟩ := by
  rw [C.germOriginal_of_outward hEuler s a ha]
  rfl

include hEuler in
theorem germRaw_twin_boundary (s : Bool) (a : Subtype (C.Frontier (!s))) :
    (C.germRawPairing s).twin (C.germBoundary s a) =
      C.germOriginal hEuler s ⟨a.val, (C.germ_vertex_port_iff hEuler s _).mpr (Or.inr a.property)⟩ := by
  rw [C.germOriginal_of_outward hEuler s _ a.property]
  rfl

end ThomGame.Pictures.PortGraph.SimpleCircuit
