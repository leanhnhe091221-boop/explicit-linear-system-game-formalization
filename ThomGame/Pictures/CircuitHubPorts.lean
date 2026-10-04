module

public import ThomGame.Pictures.SimpleCircuitMarks

/-! # The two actual hub ports at each vertex of a joint-free circuit -/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G : PortGraph P u v} [IsEmpty G.Joint] (C : G.SimpleCircuit)

theorem exists_hub_ports (k : Fin C.length) :
    ∃ (h : G.Hub) (p q : Fin (P.word (G.hubLabel h)).length),
      C.outgoing k = .hub h p ∧ C.incoming k = .hub h q ∧ p ≠ q := by
  have hv := C.incoming_vertex k
  have hn := C.incoming_ne_outgoing k
  cases ho : C.outgoing k with
  | top i =>
    cases hi : C.incoming k <;> simp_all [Port.vertex]
  | bottom i =>
    cases hi : C.incoming k <;> simp_all [Port.vertex]
  | joint j b => exact isEmptyElim j
  | hub h p =>
    cases hi : C.incoming k with
    | top i => simp_all [Port.vertex]
    | bottom i => simp_all [Port.vertex]
    | joint j b => exact isEmptyElim j
    | hub h' q =>
      have hh : h' = h := by simpa only [hi, ho, Port.vertex, Sum.inr.injEq, Sum.inl.injEq] using hv
      subst h'
      exact ⟨h, p, q, rfl, rfl,
        fun hpq => hn (hi.trans ((congrArg (Port.hub h) hpq.symm).trans ho.symm))⟩

noncomputable def hubAt (k : Fin C.length) : G.Hub := (C.exists_hub_ports k).choose

theorem hubAt_vertex (k : Fin C.length) : (C.dart k).vertex = .inr (.inl (C.hubAt k)) := by
  obtain ⟨p, q, hp, _, _⟩ := (C.exists_hub_ports k).choose_spec
  exact congrArg Port.vertex hp

theorem hubAt_injective : Function.Injective C.hubAt := by
  intro i j hij
  apply C.vertex_injective
  exact (C.hubAt_vertex i).trans ((congrArg (fun h : G.Hub => (Sum.inr (Sum.inl h) : G.Vertex)) hij).trans
    (C.hubAt_vertex j).symm)

noncomputable def hubAtRangeEquiv : Fin C.length ≃ {h : G.Hub // h ∈ Set.range C.hubAt} :=
  Equiv.ofBijective (fun k => ⟨C.hubAt k, ⟨k, rfl⟩⟩)
    ⟨fun _ _ h => C.hubAt_injective (congrArg Subtype.val h), by
      rintro ⟨h, k, hk⟩
      exact ⟨k, Subtype.ext hk⟩⟩

theorem port_eq_hubAt (k : Fin C.length) (side : Bool) :
    ∃ p : Fin (P.word (G.hubLabel (C.hubAt k))).length, C.port (k, side) = .hub (C.hubAt k) p := by
  have hv := (C.port_vertex (k, side)).trans (C.hubAt_vertex k)
  cases he : C.port (k, side) with
  | top i => simp_all [Port.vertex]
  | bottom i => simp_all [Port.vertex]
  | joint j b => exact isEmptyElim j
  | hub h p =>
    have hh : h = C.hubAt k := by simpa only [he, Port.vertex, Sum.inr.injEq, Sum.inl.injEq] using hv
    subst h
    exact ⟨p, rfl⟩

end ThomGame.Pictures.PortGraph.SimpleCircuit
