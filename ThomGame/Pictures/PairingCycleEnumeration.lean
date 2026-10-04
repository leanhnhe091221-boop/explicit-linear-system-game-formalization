module

public import ThomGame.Pictures.PairingCycles
public import ThomGame.Pictures.OrbitEnumeration

/-!
# A component of two pairings is an indexed cycle

The map from `Fin n × Bool` lists the two darts of each edge in cyclic
order. It is a bijection onto the actual connected component. Both edge
and vertex pairings are computed under this bijection, including the
one-edge loop and two-edge digon cases.
-/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

variable {D E V : Type*} [Finite D] {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel) (a : D)

noncomputable def vertexEmbedding : Fin (OrbitEnumeration.length (walk p q) a) ↪ q.Edge where
  toFun i := q.edge (OrbitEnumeration.dart (walk p q) a i)
  inj' i j he := (OrbitEnumeration.dart (walk p q) a).injective
    (vertex_injective_on_orbit p q (OrbitEnumeration.dart_sameCycle _ _ i)
      (OrbitEnumeration.dart_sameCycle _ _ j) he)

noncomputable def edgeEmbedding : Fin (OrbitEnumeration.length (walk p q) a) ↪ p.Edge where
  toFun i := p.edge (OrbitEnumeration.dart (walk p q) a i)
  inj' i j he := (OrbitEnumeration.dart (walk p q) a).injective
    (edge_injective_on_orbit p q (OrbitEnumeration.dart_sameCycle _ _ i)
      (OrbitEnumeration.dart_sameCycle _ _ j) he)

noncomputable def pairedDart : Fin (OrbitEnumeration.length (walk p q) a) × Bool → D
  | (i, false) => OrbitEnumeration.dart (walk p q) a i
  | (i, true) => p.twin (OrbitEnumeration.dart (walk p q) a i)

theorem pairedDart_edge (i : Fin (OrbitEnumeration.length (walk p q) a)) (side : Bool) :
    p.edge (pairedDart p q a (i, side)) = edgeEmbedding p q a i := by
  cases side
  · rfl
  · exact p.edge_twin _

theorem pairedDart_injective : Function.Injective (pairedDart p q a) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ he
  have hidx : edgeEmbedding p q a i = edgeEmbedding p q a j :=
    (pairedDart_edge p q a i s).symm.trans ((congrArg p.edge he).trans (pairedDart_edge p q a j t))
  have hij := (edgeEmbedding p q a).injective hidx
  subst j
  cases s <;> cases t
  · rfl
  · exact (p.ne_self _ he.symm).elim
  · exact (p.ne_self _ he).elim
  · rfl

theorem connected_iff_pairedDart (b : D) :
    RibbonConnectivity.Connected p.perm q.perm a b ↔ b ∈ Set.range (pairedDart p q a) := by
  rw [connected_iff]
  constructor
  · rintro (h | h)
    · obtain ⟨i, hi⟩ := (OrbitEnumeration.dart_range (walk p q) a b).mpr h
      exact ⟨(i, false), hi⟩
    · have hr := reverse_sameCycle p q h
      rw [p.involutive] at hr
      obtain ⟨i, hi⟩ := (OrbitEnumeration.dart_range (walk p q) a (p.twin b)).mpr hr
      refine ⟨(i, true), ?_⟩
      change p.twin (OrbitEnumeration.dart (walk p q) a i) = b
      rw [hi, p.involutive]
  · rintro ⟨⟨i, side⟩, rfl⟩
    cases side
    · exact Or.inl (OrbitEnumeration.dart_sameCycle _ _ i)
    · exact Or.inr (reverse_sameCycle p q (OrbitEnumeration.dart_sameCycle _ _ i))

noncomputable def componentEquiv :
    Fin (OrbitEnumeration.length (walk p q) a) × Bool ≃
      {b : D // RibbonConnectivity.Connected p.perm q.perm a b} :=
  Equiv.ofBijective
    (fun x => ⟨pairedDart p q a x, (connected_iff_pairedDart p q a _).mpr ⟨x, rfl⟩⟩)
    ⟨fun _ _ h => pairedDart_injective p q a (congrArg Subtype.val h), by
      intro b
      obtain ⟨x, hx⟩ := (connected_iff_pairedDart p q a b.val).mp b.property
      exact ⟨x, Subtype.ext hx⟩⟩

omit [Finite D] in
theorem pairedDart_twin (i : Fin (OrbitEnumeration.length (walk p q) a)) (side : Bool) :
    p.twin (pairedDart p q a (i, side)) = pairedDart p q a (i, !side) := by
  cases side
  · rfl
  · exact p.involutive _

omit [Finite D] in
theorem pairedDart_vertex_true (i : Fin (OrbitEnumeration.length (walk p q) a)) :
    q.twin (pairedDart p q a (i, true)) =
      pairedDart p q a (finRotate (OrbitEnumeration.length (walk p q) a) i, false) :=
  (OrbitEnumeration.dart_next (walk p q) a i).symm

omit [Finite D] in
theorem pairedDart_vertex_false (i : Fin (OrbitEnumeration.length (walk p q) a)) :
    q.twin (pairedDart p q a (i, false)) =
      pairedDart p q a ((finRotate (OrbitEnumeration.length (walk p q) a)).symm i, true) := by
  have he := pairedDart_vertex_true p q a ((finRotate _).symm i)
  rw [Equiv.apply_symm_apply] at he
  have hh := congrArg q.twin he
  rw [q.involutive] at hh
  exact hh.symm

end ThomGame.Pictures.PairingCycles
