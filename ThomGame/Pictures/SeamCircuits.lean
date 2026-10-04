module

public import ThomGame.Pictures.CircuitComposition
public import Mathlib.Data.List.FinRange

/-!
# Numbered seam gluing and its exact circuit count

The seam permutation of vertical composition is the product of its actual
numbered transpositions. Partial gluing retains the full original dart
set, allowing the cut/join theorem to apply at every step. This accounts
for all circuits but does not yet prove a planar boundary-order invariant.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}

noncomputable def seamPermutation (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) : Equiv.Perm (G.Dart ⊕ H.Dart) :=
  (l.map (fun i => Equiv.swap (.inl (.bottom i)) (.inr (.top i)))).prod

theorem seamPermutation_nil (G : PortGraph P u v) (H : PortGraph P v w) :
    seamPermutation G H [] = 1 := rfl

theorem seamPermutation_cons (G : PortGraph P u v) (H : PortGraph P v w)
    (i : Fin v.length) (l : List (Fin v.length)) :
    seamPermutation G H (i :: l) =
      Equiv.swap (.inl (.bottom i)) (.inr (.top i)) * seamPermutation G H l := rfl

theorem seamPermutation_boundary (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) (hl : l.Nodup) (i : Fin v.length) :
    (seamPermutation G H l (.inl (.bottom i)) =
      if i ∈ l then .inr (.top i) else .inl (.bottom i)) ∧
    (seamPermutation G H l (.inr (.top i)) =
      if i ∈ l then .inl (.bottom i) else .inr (.top i)) := by
  induction l with
  | nil => simp [seamPermutation_nil]
  | cons k l ih =>
    obtain ⟨hk, hl⟩ := List.nodup_cons.mp hl
    have hi := ih hl
    by_cases hik : i = k
    · subst k
      simp [seamPermutation_cons, Equiv.Perm.mul_apply, hi.1, hi.2, hk]
    · by_cases hil : i ∈ l
      · simp [seamPermutation_cons, Equiv.Perm.mul_apply, hi.1, hi.2, hil,
          Equiv.swap_apply_def, hik]
      · simp [seamPermutation_cons, Equiv.Perm.mul_apply, hi.1, hi.2, hil,
          Equiv.swap_apply_def, hik]

theorem seamPermutation_fixed (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) (a : G.Dart ⊕ H.Dart)
    (ha : ∀ i : Fin v.length, a ≠ .inl (.bottom i) ∧ a ≠ .inr (.top i)) :
    seamPermutation G H l a = a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [seamPermutation_cons, Equiv.Perm.mul_apply, ih,
      Equiv.swap_apply_of_ne_of_ne (ha i).1 (ha i).2]

theorem seamPermutation_all (G : PortGraph P u v) (H : PortGraph P v w) :
    seamPermutation G H (List.finRange v.length) = seamSwap G H := by
  apply Equiv.ext
  rintro (a | a)
  · cases a with
    | bottom i =>
      simpa [seamSwap] using (seamPermutation_boundary G H _ (List.nodup_finRange _) i).1
    | top i => exact seamPermutation_fixed G H _ _ (by intro k; simp)
    | hub h i => exact seamPermutation_fixed G H _ _ (by intro k; simp)
    | joint j side => exact seamPermutation_fixed G H _ _ (by intro k; simp)
  · cases a with
    | top i =>
      simpa [seamSwap] using (seamPermutation_boundary G H _ (List.nodup_finRange _) i).2
    | bottom i => exact seamPermutation_fixed G H _ _ (by intro k; simp)
    | hub h i => exact seamPermutation_fixed G H _ _ (by intro k; simp)
    | joint j side => exact seamPermutation_fixed G H _ _ (by intro k; simp)

theorem seamPermutation_eq_of_mem_iff (G : PortGraph P u v) (H : PortGraph P v w)
    {l m : List (Fin v.length)} (hl : l.Nodup) (hm : m.Nodup)
    (hmem : ∀ i, i ∈ l ↔ i ∈ m) : seamPermutation G H l = seamPermutation G H m := by
  apply Equiv.ext
  rintro (a | a)
  · cases a with
    | bottom i =>
      rw [(seamPermutation_boundary G H l hl i).1,
        (seamPermutation_boundary G H m hm i).1]
      simp only [hmem i]
    | top i =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]
    | hub h i =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]
    | joint j side =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]
  · cases a with
    | top i =>
      rw [(seamPermutation_boundary G H l hl i).2,
        (seamPermutation_boundary G H m hm i).2]
      simp only [hmem i]
    | bottom i =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]
    | hub h i =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]
    | joint j side =>
      rw [seamPermutation_fixed G H l _ (by intro k; simp),
        seamPermutation_fixed G H m _ (by intro k; simp)]

/-- Circuit permutation after gluing just the listed seams, from tail to head. -/
noncomputable def seamCircuit (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) : Equiv.Perm (G.Dart ⊕ H.Dart) :=
  seamPermutation G H l * Equiv.sumCongr G.circuitStep H.circuitStep

theorem seamCircuit_nil (G : PortGraph P u v) (H : PortGraph P v w) :
    seamCircuit G H [] = Equiv.sumCongr G.circuitStep H.circuitStep := by
  simp [seamCircuit, seamPermutation_nil]

theorem seamCircuit_cons (G : PortGraph P u v) (H : PortGraph P v w)
    (i : Fin v.length) (l : List (Fin v.length)) :
    seamCircuit G H (i :: l) =
      CycleSurgery.splice (seamCircuit G H l) (.inl (.bottom i)) (.inr (.top i)) := by
  simp only [seamCircuit, seamPermutation_cons, CycleSurgery.splice, mul_assoc]

theorem seamCircuit_all (G : PortGraph P u v) (H : PortGraph P v w)
    (a : G.Dart ⊕ H.Dart) :
    (G.comp H).circuitStep (compPorts G H a) =
      compPorts G H (seamCircuit G H (List.finRange v.length) a) := by
  have he := circuitStep_compPorts G H a
  simpa only [seamCircuit, seamPermutation_all, Equiv.Perm.mul_apply] using he

noncomputable def seamCircuitEquiv (G : PortGraph P u v) (H : PortGraph P v w) :
    FiniteReturn.Orbit (seamCircuit G H (List.finRange v.length)) ≃ (G.comp H).Circuit :=
  FiniteReturn.orbitEquiv _ _ (compPorts G H) (seamCircuit_all G H)

theorem seamCircuit_sameCycle_iff (G : PortGraph P u v) (H : PortGraph P v w)
    (a b : G.Dart ⊕ H.Dart) :
    (seamCircuit G H (List.finRange v.length)).SameCycle a b ↔
      (G.comp H).circuit (compPorts G H a) = (G.comp H).circuit (compPorts G H b) :=
  (FiniteReturn.sameCycle_congr _ _ (compPorts G H) (seamCircuit_all G H) a b).trans
    ((G.comp H).circuit_eq_iff _ _).symm

/-- Number of steps that split a circuit in the specified gluing sequence. -/
noncomputable def seamSplits (G : PortGraph P u v) (H : PortGraph P v w) :
    List (Fin v.length) → Nat
  | [] => 0
  | i :: l => seamSplits G H l +
      if (seamCircuit G H l).SameCycle (.inl (.bottom i)) (.inr (.top i)) then 1 else 0

theorem seam_circuit_card (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) :
    Nat.card (FiniteReturn.Orbit (seamCircuit G H l)) + l.length =
      Fintype.card G.Circuit + Fintype.card H.Circuit + 2 * seamSplits G H l := by
  simp only [← Nat.card_eq_fintype_card]
  induction l with
  | nil =>
    rw [seamCircuit_nil, FiniteReturn.orbit_card_sum]
    simp only [List.length_nil, seamSplits,
      mul_zero, Nat.add_zero]
    rfl
  | cons i l ih =>
    rw [seamCircuit_cons, List.length_cons, seamSplits]
    by_cases h : (seamCircuit G H l).SameCycle (.inl (.bottom i)) (.inr (.top i))
    · rw [ite_eq_left h, CycleSurgery.orbit_card_split _ (by simp) h]
      omega
    · rw [ite_eq_right h]
      have hc := CycleSurgery.orbit_card_join (seamCircuit G H l) h
      omega

theorem comp_circuit_card (G : PortGraph P u v) (H : PortGraph P v w) :
    Fintype.card (G.comp H).Circuit + v.length =
      Fintype.card G.Circuit + Fintype.card H.Circuit +
        2 * seamSplits G H (List.finRange v.length) := by
  have hc := seam_circuit_card G H (List.finRange v.length)
  have he := Nat.card_congr (seamCircuitEquiv G H)
  simp only [List.length_finRange, Nat.card_eq_fintype_card] at hc he
  omega

theorem seamSplits_singleton (G : PortGraph P u v) (H : PortGraph P v w)
    (i : Fin v.length) : seamSplits G H [i] = 0 := by
  simp [seamSplits, seamCircuit_nil, FiniteReturn.sum_not_sameCycle]

theorem singleton_seam_circuit_card (G : PortGraph P u v) (H : PortGraph P v w)
    (i : Fin v.length) :
    Nat.card (FiniteReturn.Orbit (seamCircuit G H [i])) + 1 =
      Fintype.card G.Circuit + Fintype.card H.Circuit := by
  simpa only [List.length_singleton, seamSplits_singleton, mul_zero, Nat.add_zero]
    using seam_circuit_card G H [i]

theorem seamSplits_le_length (G : PortGraph P u v) (H : PortGraph P v w)
    (l : List (Fin v.length)) : seamSplits G H l ≤ l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [seamSplits, List.length_cons]
    split_ifs <;> omega

/-- Although the intermediate circuits can differ, the number of splits
is independent of the order in which a fixed set of seams is glued. -/
theorem seamSplits_perm (G : PortGraph P u v) (H : PortGraph P v w)
    {l m : List (Fin v.length)} (hl : l.Nodup) (h : l.Perm m) :
    seamSplits G H l = seamSplits G H m := by
  have he : seamCircuit G H l = seamCircuit G H m := by
    unfold seamCircuit
    rw [seamPermutation_eq_of_mem_iff G H hl (h.nodup_iff.mp hl) (fun _ => h.mem_iff)]
  have hc := seam_circuit_card G H l
  have hd := seam_circuit_card G H m
  rw [he, h.length_eq] at hc
  omega

end ThomGame.Pictures.PortGraph
