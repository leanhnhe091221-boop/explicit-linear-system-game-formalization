module

public import ThomGame.Pictures.WheelCopyAssembly

/-!
# A whole-wheel lift is an entire auxiliary-edge component

Connectivity here is the equivalence closure of actual edge twins whose
labels are auxiliary columns. All eight auxiliary port types remain in a
lift, and its central ring connects its three families of hubs. Thus a
lift contains exactly one whole component, with one hub over each wheel row.
-/

@[expose] public section
namespace ThomGame.Wheel.Family

open Pictures PortGraph Equiv
open scoped Classical BigOperators

variable {R V R' V' : Type*} (F : Family R V)
  (rows : F.Row ≃ R') (cols : F.Col ≃ V')
  (G : SolutionGroup.RowGraph (F.system.reindex rows cols) [] [])

def AuxiliaryAdj (h k : G.Hub) : Prop :=
  ∃ (p q : Fin 3) (a : F.Auxiliary),
    G.pairing.twin (.hub h p) = .hub k q ∧
      Port.label G.jointLabel (.hub h p : G.Dart) = cols (.inr a)

def AuxiliaryConnected : G.Hub → G.Hub → Prop :=
  Relation.EqvGen (F.AuxiliaryAdj rows cols G)

theorem auxiliaryAdj_symm {h k : G.Hub} (hk : F.AuxiliaryAdj rows cols G h k) :
    F.AuxiliaryAdj rows cols G k h := by
  obtain ⟨p, q, a, ht, hl⟩ := hk
  refine ⟨q, p, a, ?_, ?_⟩
  · exact (congrArg G.pairing.twin ht).symm.trans (G.pairing.involutive _)
  · exact (congrArg (Port.label G.jointLabel) ht).symm.trans
      ((G.pairing.label_twin _).trans hl)

namespace GraphLift

variable {F rows cols G} {r : R} (L : F.GraphLift rows cols G r)

def Contains (h : G.Hub) : Prop := ∃ j k, L.hub j k = h

theorem hub_injective : Function.Injective (fun x : Fin (F.size r) × Fin 3 => L.hub x.1 x.2) := by
  intro x y hxy
  have hh := rows.injective ((L.label x.1 x.2).symm.trans
    ((congrArg G.hubLabel hxy).trans (L.label y.1 y.2)))
  simpa using hh

theorem auxiliary_twin (j : Fin (F.size r)) (k p : Fin 3) (hp : ¬ (k = 0 ∧ p = 0)) :
    ∃ (i : Fin (F.size r)) (l q : Fin 3),
      G.pairing.twin (.hub (L.hub j k) p) = .hub (L.hub i l) q := by
  have rev {x y : G.Dart} (h : G.pairing.twin x = y) : G.pairing.twin y = x :=
    (congrArg G.pairing.twin h).symm.trans (G.pairing.involutive x)
  fin_cases k <;> fin_cases p
  · exact (hp ⟨rfl, rfl⟩).elim
  · exact ⟨_, 1, 2, L.twin_a j⟩
  · exact ⟨j, 1, 0, L.twin_b j⟩
  · exact ⟨j, 0, 2, rev (L.twin_b j)⟩
  · exact ⟨j, 2, 0, L.twin_c j⟩
  · have ha := L.twin_a (finRotate (F.size r) j)
    have he := congrArg (fun i => (.hub (L.hub i 1) (2 : Fin 3) : G.Dart))
      ((finRotate (F.size r)).symm_apply_apply j)
    exact ⟨_, 0, 1, rev (ha.trans he)⟩
  · exact ⟨j, 1, 1, rev (L.twin_c j)⟩
  · exact ⟨_, 2, 2, L.twin_d j⟩
  · have hd := L.twin_d (finRotate (F.size r) j)
    have he := congrArg (fun i => (.hub (L.hub i 2) (2 : Fin 3) : G.Dart))
      ((finRotate (F.size r)).symm_apply_apply j)
    exact ⟨_, 2, 1, rev (hd.trans he)⟩

theorem contains_of_adj {h k : G.Hub} (hh : L.Contains h)
    (hk : F.AuxiliaryAdj rows cols G h k) : L.Contains k := by
  obtain ⟨j, l, rfl⟩ := hh
  obtain ⟨p, q, a, ht, hl⟩ := hk
  have hp : ¬ (l = 0 ∧ p = 0) := by
    rintro ⟨rfl, rfl⟩
    have he : Port.label G.jointLabel (.hub (L.hub j 0) (0 : Fin 3) : G.Dart) =
        cols (.inl (F.letter r j)) := by
      rw [SolutionGroup.rowGraph_port_label, L.label, SparseSystem.reindex_column]
      rfl
    have hx := cols.injective (he.symm.trans hl)
    cases hx
  obtain ⟨i, m, t, hi⟩ := L.auxiliary_twin j l p hp
  exact ⟨i, m, Sum.inl.inj (Sum.inr.inj (congrArg Port.vertex (hi.symm.trans ht)))⟩

theorem contains_iff_of_connected {h k : G.Hub}
    (hk : F.AuxiliaryConnected rows cols G h k) : L.Contains h ↔ L.Contains k := by
  induction hk with
  | rel h k hk =>
    exact ⟨fun hh => L.contains_of_adj hh hk,
      fun hh => L.contains_of_adj hh (F.auxiliaryAdj_symm rows cols G hk)⟩
  | refl h => rfl
  | symm h k _ ih => exact ih.symm
  | trans h k l _ _ ih ik => exact ih.trans ik

theorem connected_of_twin (j i : Fin (F.size r)) (k l p q : Fin 3)
    (hp : ¬ (k = 0 ∧ p = 0))
    (ht : G.pairing.twin (.hub (L.hub j k) p) = .hub (L.hub i l) q) :
    F.AuxiliaryConnected rows cols G (L.hub j k) (L.hub i l) := by
  apply Relation.EqvGen.rel
  refine ⟨p, q, ?_⟩
  have he : Port.label G.jointLabel (.hub (L.hub j k) p : G.Dart) =
      cols (F.columns r j k p) := by
    rw [SolutionGroup.rowGraph_port_label, L.label, SparseSystem.reindex_column]
    rfl
  have ha : ∃ a : F.Auxiliary, F.columns r j k p = .inr a := by
    fin_cases k <;> fin_cases p
    · exact (hp ⟨rfl, rfl⟩).elim
    all_goals exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := ha
  exact ⟨a, ht, he.trans (congrArg cols ha)⟩

theorem connected_to_central (j : Fin (F.size r)) (k : Fin 3) :
    F.AuxiliaryConnected rows cols G (L.hub j k) (L.hub j 2) := by
  have hb := L.connected_of_twin j j 0 1 2 0 (by decide) (L.twin_b j)
  have hc := L.connected_of_twin j j 1 2 1 0 (by decide) (L.twin_c j)
  fin_cases k
  · exact Relation.EqvGen.trans _ _ _ hb hc
  · exact hc
  · exact Relation.EqvGen.refl _

theorem central_connected (i j : Fin (F.size r)) :
    F.AuxiliaryConnected rows cols G (L.hub i 2) (L.hub j 2) := by
  have step (k : Fin (F.size r)) :
      F.AuxiliaryConnected rows cols G (L.hub k 2) (L.hub (finRotate (F.size r) k) 2) := by
    have hh := L.connected_of_twin (finRotate (F.size r) k)
      ((finRotate (F.size r)).symm (finRotate (F.size r) k)) 2 2 1 2 (by decide)
      (L.twin_d (finRotate (F.size r) k))
    simp only [symm_apply_apply] at hh
    exact Relation.EqvGen.symm _ _ hh
  obtain ⟨m, hm⟩ := (finRotate_sameCycle i j).exists_nat_pow_eq
  rw [← hm]
  clear hm
  induction m with
  | zero => exact Relation.EqvGen.refl _
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih (step _)

theorem hubs_connected (i j : Fin (F.size r)) (k l : Fin 3) :
    F.AuxiliaryConnected rows cols G (L.hub i k) (L.hub j l) :=
  Relation.EqvGen.trans _ _ _ (L.connected_to_central i k)
    (Relation.EqvGen.trans _ _ _ (L.central_connected i j)
      (Relation.EqvGen.symm _ _ (L.connected_to_central j l)))

theorem contains_iff_connected (i : Fin (F.size r)) (k : Fin 3) (h : G.Hub) :
    L.Contains h ↔ F.AuxiliaryConnected rows cols G (L.hub i k) h := by
  constructor
  · rintro ⟨j, l, rfl⟩
    exact L.hubs_connected i j k l
  · intro hh
    exact (L.contains_iff_of_connected hh).mp ⟨i, k, rfl⟩

theorem unique_hub_over_row (j : Fin (F.size r)) (k : Fin 3) :
    ∃! h : G.Hub, L.Contains h ∧ G.hubLabel h = rows ⟨r, j, k⟩ := by
  refine ⟨L.hub j k, ⟨⟨j, k, rfl⟩, L.label j k⟩, ?_⟩
  rintro h ⟨⟨i, l, rfl⟩, hh⟩
  have he := rows.injective ((L.label i l).symm.trans hh)
  have hp : (i, l) = (j, k) := by simpa using he
  exact congrArg (fun x : Fin (F.size r) × Fin 3 => L.hub x.1 x.2) hp

noncomputable def componentEquiv (i : Fin (F.size r)) (k : Fin 3) :
    (Fin (F.size r) × Fin 3) ≃ {h : G.Hub // F.AuxiliaryConnected rows cols G (L.hub i k) h} :=
  Equiv.ofBijective (fun x => ⟨L.hub x.1 x.2, L.hubs_connected i x.1 k x.2⟩)
    ⟨fun _ _ hh => L.hub_injective (congrArg Subtype.val hh), by
      rintro ⟨h, hh⟩
      obtain ⟨j, l, hj⟩ := (L.contains_iff_connected i k h).mpr hh
      exact ⟨(j, l), Subtype.ext hj⟩⟩

theorem component_card (i : Fin (F.size r)) (k : Fin 3) :
    Fintype.card {h : G.Hub // F.AuxiliaryConnected rows cols G (L.hub i k) h} = 3 * F.size r := by
  classical
  rw [← Fintype.card_congr (L.componentEquiv i k)]
  simp [Nat.mul_comm]

theorem component_sum (i : Fin (F.size r)) (k : Fin 3) (χ : R' → ZMod 2) :
    (∑ h : {h : G.Hub // F.AuxiliaryConnected rows cols G (L.hub i k) h}, χ (G.hubLabel h.val)) =
      ∑ j : Fin (F.size r), ∑ l : Fin 3, χ (rows ⟨r, j, l⟩) := by
  rw [← (L.componentEquiv i k).sum_comp (fun h => χ (G.hubLabel h.val))]
  change (∑ x : Fin (F.size r) × Fin 3, χ (G.hubLabel (L.hub x.1 x.2))) = _
  simp_rw [L.label]
  exact Fintype.sum_prod_type _

theorem component_rhs_sum (i : Fin (F.size r)) (k : Fin 3) :
    (∑ h : {h : G.Hub // F.AuxiliaryConnected rows cols G (L.hub i k) h},
      (F.system.reindex rows cols).rhs (G.hubLabel h.val)) = F.parity r := by
  rw [L.component_sum]
  simp only [SparseSystem.reindex_rhs]
  simp [system, Fin.sum_univ_succ]
  change (∑ j : Fin (F.size r), if j = (0 : Fin (F.size r)) then F.parity r else 0) = _
  simp

end GraphLift
end ThomGame.Wheel.Family
