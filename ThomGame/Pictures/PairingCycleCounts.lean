module

public import ThomGame.Pictures.PairingCycles

/-! # Exactly two oriented walk orbits per paired-cycle component -/

@[expose] public section
namespace ThomGame.Pictures.PairingCycles

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

variable {D E V : Type*} {edgeLabel : D → E} {vertexLabel : D → V}
  (p : Pairing edgeLabel) (q : Pairing vertexLabel) [Finite D]

noncomputable def orbitComponent : Orbit (walk p q) → Component p.perm q.perm :=
  Quotient.lift (component p.perm q.perm)
    (fun _ _ h => (component_eq_iff _ _ _ _).mpr (sameCycle_connected p q h))

noncomputable def orientationOrbit (c : Component p.perm q.perm) : Bool → Orbit (walk p q)
  | false => orbit (walk p q) c.out
  | true => orbit (walk p q) (p.twin c.out)

theorem orientationOrbit_component (c : Component p.perm q.perm) (side : Bool) :
    orbitComponent p q (orientationOrbit p q c side) = c := by
  cases side
  · exact Quotient.out_eq c
  · exact (component_edge p.perm q.perm c.out).trans (Quotient.out_eq c)

noncomputable def orientedComponentEquiv : Component p.perm q.perm × Bool ≃ Orbit (walk p q) :=
  Equiv.ofBijective (fun x => orientationOrbit p q x.1 x.2) ⟨by
    rintro ⟨c, s⟩ ⟨d, t⟩ he
    have hc : c = d := (orientationOrbit_component p q c s).symm.trans
      ((congrArg (orbitComponent p q) he).trans (orientationOrbit_component p q d t))
    subst d
    cases s <;> cases t
    · rfl
    · exact (not_sameCycle_edge p q c.out ((orbit_eq_iff _ _ _).mp he)).elim
    · exact (not_sameCycle_edge p q c.out ((orbit_eq_iff _ _ _).mp he.symm)).elim
    · rfl,
    by
    intro o
    refine Quotient.inductionOn o fun x => ?_
    let c := component p.perm q.perm x
    have hc : Connected p.perm q.perm c.out x := (component_eq_iff _ _ _ _).mp (Quotient.out_eq c)
    rcases (connected_iff p q c.out x).mp hc with h | h
    · exact ⟨(c, false), (orbit_eq_iff _ _ _).mpr h⟩
    · exact ⟨(c, true), (orbit_eq_iff _ _ _).mpr h⟩⟩

theorem walk_orbit_card :
    Nat.card (Orbit (walk p q)) = 2 * Nat.card (Component p.perm q.perm) := by
  rw [← Nat.card_congr (orientedComponentEquiv p q), Nat.card_prod]
  simp [Nat.mul_comm]

end ThomGame.Pictures.PairingCycles
