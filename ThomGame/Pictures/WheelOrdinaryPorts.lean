module

public import ThomGame.Pictures.WheelLiftOrientation
public import ThomGame.Pictures.FaceReturnContraction

/-!
# The actual retained ordinary-generator ports of a wheel graph

Ordinary ports are selected by their original labels, and their edge
pairing is the old pairing restricted to this invariant set. In a
joint-free closed wheel graph they are precisely slot zero at an outer
hub. Returning the original faces defines the prospective collapsed
vertex permutation and preserves Euler saturation.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph Equiv RibbonConnectivity
open scoped Classical

variable {R V R' V' : Type*} (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] [])

def IsOrdinaryPort (x : G.Dart) : Prop :=
  ∃ v : V, Port.label G.jointLabel x = cols (.inl v)

theorem ordinaryPort_twin_iff (x : G.Dart) :
    F.IsOrdinaryPort rows cols G (G.pairing.twin x) ↔ F.IsOrdinaryPort rows cols G x := by
  unfold IsOrdinaryPort
  rw [G.pairing.label_twin]

abbrev OrdinaryPort := {x : G.Dart // F.IsOrdinaryPort rows cols G x}

noncomputable def ordinaryLabel (x : F.OrdinaryPort rows cols G) : V := x.property.choose

theorem ordinaryLabel_spec (x : F.OrdinaryPort rows cols G) :
    Port.label G.jointLabel x.val = cols (.inl (F.ordinaryLabel rows cols G x)) := x.property.choose_spec

noncomputable def ordinaryPairing : Pairing (F.ordinaryLabel rows cols G) where
  twin x := ⟨G.pairing.twin x.val, (F.ordinaryPort_twin_iff rows cols G x.val).mpr x.property⟩
  involutive x := Subtype.ext (G.pairing.involutive x.val)
  ne_self x hx := G.pairing.ne_self x.val (congrArg Subtype.val hx)
  label_twin x := by
    apply Sum.inl.inj
    apply cols.injective
    exact (F.ordinaryLabel_spec rows cols G _).symm.trans
      ((G.pairing.label_twin x.val).trans (F.ordinaryLabel_spec rows cols G x))

theorem ordinaryPairing_perm : (F.ordinaryPairing rows cols G).perm =
    G.pairing.perm.subtypePerm (F.ordinaryPort_twin_iff rows cols G) := by
  ext x
  rfl

noncomputable def ordinaryRotation : Perm (F.OrdinaryPort rows cols G) :=
  MarkedReturn.perm G.circuitStep (F.IsOrdinaryPort rows cols G) * (F.ordinaryPairing rows cols G).perm

theorem ordinaryRotation_saturated
    (he : eulerDefect G.pairing.perm G.circuitStep = 0) :
    RotationEuler.count (F.ordinaryRotation rows cols G) (F.ordinaryPairing rows cols G).perm =
      2 * Nat.card (Component (F.ordinaryRotation rows cols G) (F.ordinaryPairing rows cols G).perm) := by
  have hs := FaceReturnContraction.saturated G.circuitStep G.pairing.perm
    (F.IsOrdinaryPort rows cols G) (F.ordinaryPort_twin_iff rows cols G)
    G.pairing.involutive (G.dualEuler_eq_twice_components he)
  simpa only [ordinaryRotation, F.ordinaryPairing_perm, FaceReturnContraction.rotation] using hs

theorem ordinary_hub_iff (h : G.Hub) (p : Fin 3) :
    F.IsOrdinaryPort rows cols G (.hub h p) ↔
      ∃ (r : R) (j : Fin (F.size r)), G.hubLabel h = rows ⟨r, j, 0⟩ ∧ p = 0 := by
  obtain ⟨⟨r, j, k⟩, hr⟩ := rows.surjective (G.hubLabel h)
  have hl : Port.label G.jointLabel (.hub h p : G.Dart) = cols (F.columns r j k p) := by
    rw [SolutionGroup.rowGraph_port_label, ← hr, SparseSystem.reindex_column]
    rfl
  constructor
  · rintro ⟨v, hv⟩
    have hx := cols.injective (hl.symm.trans hv)
    fin_cases k <;> fin_cases p
    · exact ⟨r, j, hr.symm, rfl⟩
    all_goals cases hx
  · rintro ⟨s, i, hs, rfl⟩
    refine ⟨F.letter s i, ?_⟩
    rw [SolutionGroup.rowGraph_port_label, hs, SparseSystem.reindex_column]
    rfl

variable [IsEmpty G.Joint]

theorem ordinaryPort_exists_hub (x : F.OrdinaryPort rows cols G) :
    ∃ (h : G.Hub) (r : R) (j : Fin (F.size r)),
      x.val = .hub h (0 : Fin 3) ∧ G.hubLabel h = rows ⟨r, j, 0⟩ := by
  rcases x with ⟨x, hx⟩
  cases x with
  | top i => exact i.elim0
  | bottom i => exact i.elim0
  | joint j b =>
    have hf : False := isEmptyElim j
    exact hf.elim
  | hub h p =>
    obtain ⟨r, j, hl, hp⟩ := (F.ordinary_hub_iff rows cols G h p).mp hx
    exact ⟨h, r, j, congrArg (fun i : Fin 3 => (.hub h i : G.Dart)) hp, hl⟩

end ThomGame.Wheel.Family

namespace ThomGame.Wheel.Family.GraphLift

open Pictures PortGraph

variable {R V R' V' : Type*} {F : Family R V}
  {rows : F.Row ≃ R'} {cols : F.Col ≃ V'}
  {G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] []}
  {r : R} (L : F.GraphLift rows cols G r)

theorem ordinary_port_iff (j : Fin (F.size r)) (k p : Fin 3) :
    F.IsOrdinaryPort rows cols G (.hub (L.hub j k) p) ↔ k = 0 ∧ p = 0 := by
  rw [F.ordinary_hub_iff]
  constructor
  · rintro ⟨s, i, hs, hp⟩
    have hh := rows.injective ((L.label j k).symm.trans hs)
    exact ⟨by cases hh; rfl, hp⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨r, j, L.label j 0, rfl⟩

def ordinaryPort (j : Fin (F.size r)) : F.OrdinaryPort rows cols G :=
  ⟨.hub (L.hub j 0) (0 : Fin 3), (L.ordinary_port_iff j 0 0).mpr ⟨rfl, rfl⟩⟩

theorem ordinaryPort_label (j : Fin (F.size r)) :
    F.ordinaryLabel rows cols G (L.ordinaryPort j) = F.letter r j := by
  apply Sum.inl.inj
  apply cols.injective
  exact (F.ordinaryLabel_spec rows cols G (L.ordinaryPort j)).symm.trans (L.port_label j 0 0)

end ThomGame.Wheel.Family.GraphLift
