module

public import ThomGame.Pictures.SunBandErasureAccounting
public import ThomGame.Pictures.OrderedPairingPorts

/-!
# Actual surviving ports after erasing a three-label sun circuit

Every original unmarked port survives exactly once. Off-circuit hubs
are retained and the remaining ports at each spoke pair form one new
two-port joint. Boundary ports retain their exact original positions.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

abbrev SunBandErasureJoint := (C.sunBandExternalPairing hn i hband).OrderedEdge

abbrev SunBandErasureDart := Port (sunPresentation n b) u v C.ErasedCircuitHub
  (C.SunBandErasureJoint hn i hband) (fun h => G.hubLabel h.val)

noncomputable def sunBandErasurePort : C.SunBandErasureDart hn i hband → G.Dart
  | .top j => .top j
  | .bottom j => .bottom j
  | .hub h p => .hub h.val p
  | .joint j side => C.sunBandExternalPort i ((C.sunBandExternalPairing hn i hband).orderedPorts (j, side))

theorem sunBandErasurePort_unmarked (x : C.SunBandErasureDart hn i hband) :
    ¬ C.Marked (C.sunBandErasurePort hn i hband x) := by
  cases x with
  | top j =>
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | bottom j =>
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨p, hp⟩ := C.port_eq_hubAt k side
    cases hp.symm.trans he
  | hub h p =>
    rintro ⟨⟨k, side⟩, he⟩
    obtain ⟨q, hq⟩ := C.port_eq_hubAt k side
    exact h.property ⟨k, (G.sun_hub_eq_iff.mp (hq.symm.trans he)).1⟩
  | joint j side => exact C.sunBandExternalPort_unmarked hn i hband _

theorem sunBandErasurePort_injective : Function.Injective (C.sunBandErasurePort hn i hband) := by
  intro x y he
  cases x with
  | top j =>
    cases y with
    | top k => exact congrArg Port.top (Port.top.inj he)
    | bottom k => cases he
    | hub h p => cases he
    | joint k side => cases he
  | bottom j =>
    cases y with
    | top k => cases he
    | bottom k => exact congrArg Port.bottom (Port.bottom.inj he)
    | hub h p => cases he
    | joint k side => cases he
  | hub h p =>
    cases y with
    | top k => cases he
    | bottom k => cases he
    | hub k q =>
      obtain ⟨hh, hp⟩ := G.sun_hub_eq_iff.mp he
      have hh' : h = k := Subtype.ext hh
      subst k
      exact congrArg (Port.hub h) hp
    | joint j side =>
      have hh := (G.sun_hub_eq_iff.mp he).1
      exact (h.property ⟨_, hh.symm⟩).elim
  | joint j side =>
    cases y with
    | top k => cases he
    | bottom k => cases he
    | hub h p =>
      have hh := (G.sun_hub_eq_iff.mp he).1
      exact (h.property ⟨_, hh⟩).elim
    | joint k t =>
      have hx := (C.sunBandExternalPairing hn i hband).orderedPorts.injective
        (C.sunBandExternalPort_injective i he)
      exact congrArg (fun z : C.SunBandErasureJoint hn i hband × Bool =>
        (Port.joint z.1 z.2 : C.SunBandErasureDart hn i hband)) hx

theorem sunBandErasurePort_surjective (x : G.Dart) (hx : ¬ C.Marked x) :
    ∃ y : C.SunBandErasureDart hn i hband, C.sunBandErasurePort hn i hband y = x := by
  cases x with
  | top j => exact ⟨.top j, rfl⟩
  | bottom j => exact ⟨.bottom j, rfl⟩
  | joint j side => exact isEmptyElim j
  | hub h p =>
    by_cases hh : h ∈ Set.range C.hubAt
    · obtain ⟨k, hk⟩ := hh
      have hv : (Port.hub h p : G.Dart).vertex = (C.dart k).vertex := by
        rw [C.hubAt_vertex, hk]
        rfl
      have he := C.sunBandExternalPort_unique hn i hband k (.hub h p) hv hx
      obtain ⟨⟨j, side⟩, hj⟩ := (C.sunBandExternalPairing hn i hband).orderedPorts.surjective k
      exact ⟨.joint j side, (congrArg (C.sunBandExternalPort i) hj).trans he.symm⟩
    · exact ⟨.hub ⟨h, hh⟩ p, rfl⟩

noncomputable def sunBandErasurePorts :
    C.SunBandErasureDart hn i hband ≃ {x : G.Dart // ¬ C.Marked x} :=
  Equiv.ofBijective (fun x => ⟨C.sunBandErasurePort hn i hband x,
    C.sunBandErasurePort_unmarked hn i hband x⟩)
    ⟨fun _ _ h => C.sunBandErasurePort_injective hn i hband (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := C.sunBandErasurePort_surjective hn i hband x hx
      exact ⟨y, Subtype.ext hy⟩⟩

noncomputable def sunBandErasureJointLabel (j : C.SunBandErasureJoint hn i hband) : Fin n ⊕ Fin n :=
  Port.label G.jointLabel (C.sunBandExternalPort i j.val)

theorem sunBandErasurePort_label (x : C.SunBandErasureDart hn i hband) :
    Port.label G.jointLabel (C.sunBandErasurePort hn i hband x) =
      Port.label (C.sunBandErasureJointLabel hn i hband) x := by
  cases x with
  | top j => rfl
  | bottom j => rfl
  | hub h p => rfl
  | joint j side => exact (C.sunBandExternalPairing hn i hband).orderedPort_label j side

end ThomGame.Pictures.PortGraph.SimpleCircuit
