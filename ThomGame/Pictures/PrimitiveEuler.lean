module

public import ThomGame.Pictures.GraphComponentCounts

/-!
# Euler defect of the five primitive graphs

The dart count handles an empty relation word separately: its zero-port
hub contributes no dart orbit. For a nonempty relation, all darts lie on
one circuit and the actual vertex and edge counts give defect zero.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

namespace FiniteReturn

def orbitOneEquiv (A : Type*) : Orbit (1 : Perm A) ≃ A where
  toFun := Quotient.lift id (fun _ _ h => Perm.sameCycle_one.mp h)
  invFun := orbit 1
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv _ := rfl

theorem orbit_card_of_one_cycle {A : Type*} (f : Perm A) (a : A)
    (h : ∀ x y, f.SameCycle x y) : Nat.card (Orbit f) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨orbit f a, ?_⟩
  intro c
  exact Quotient.inductionOn c (fun x => (orbit_eq_iff f x a).mpr (h x a))

end FiniteReturn

namespace RibbonConnectivity

theorem component_card_of_one_cycle {A : Type*} [Finite A] (p f : Perm A) (a : A)
    (h : ∀ x y, f.SameCycle x y) : Nat.card (Component p f) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨component p f a, ?_⟩
  intro c
  exact Quotient.inductionOn c (fun x => (component_eq_iff p f x a).mpr (sameCycle_connected p f (h x a)))

theorem eulerDefect_of_empty {A : Type*} [Finite A] [IsEmpty A] (p f : Perm A) :
    eulerDefect p f = 0 := by
  simp [eulerDefect, eulerCount, Component, Orbit]

end RibbonConnectivity

namespace PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem eulerDefect_of_no_internal (G : PortGraph P u v) [IsEmpty G.Hub] [IsEmpty G.Joint] :
    eulerDefect G.pairing.perm G.circuitStep = 0 := by
  rw [G.circuitStep_eq_pairing_of_no_internal]
  have hp : G.pairing.perm * G.pairing.perm = 1 := by
    ext a
    exact G.pairing.involutive a
  have hc : Nat.card (Component G.pairing.perm G.pairing.perm) = Nat.card (Orbit G.pairing.perm) :=
    Nat.card_congr (Quotient.congr (Equiv.refl G.Dart) (connected_self_iff_sameCycle G.pairing.perm))
  have hd : Nat.card G.Dart = 2 * Nat.card G.Edge := by
    simpa only [Nat.card_eq_fintype_card] using G.pairing.dart_card_eq_twice_edge_card
  unfold eulerDefect eulerCount
  rw [hp, Nat.card_congr (orbitOneEquiv G.Dart), hc, Nat.card_congr G.edgeOrbitEquiv]
  omega

theorem eulerDefect_identity (P : InvolutionPresentation R S) (w : List S) :
    eulerDefect (identity P w).pairing.perm (identity P w).circuitStep = 0 := by
  let : IsEmpty (identity P w).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (identity P w).Joint := by change IsEmpty Empty; infer_instance
  exact eulerDefect_of_no_internal _

theorem eulerDefect_cap (P : InvolutionPresentation R S) (s : S) :
    eulerDefect (cap P s).pairing.perm (cap P s).circuitStep = 0 := by
  let : IsEmpty (cap P s).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (cap P s).Joint := by change IsEmpty Empty; infer_instance
  exact eulerDefect_of_no_internal _

theorem eulerDefect_cup (P : InvolutionPresentation R S) (s : S) :
    eulerDefect (cup P s).pairing.perm (cup P s).circuitStep = 0 := by
  let : IsEmpty (cup P s).Hub := by change IsEmpty Empty; infer_instance
  let : IsEmpty (cup P s).Joint := by change IsEmpty Empty; infer_instance
  exact eulerDefect_of_no_internal _

theorem circuitStep_down_to_top (P : InvolutionPresentation R S) (r : R) (a : (down P r).Dart) :
    ∃ i, (down P r).circuitStep.SameCycle a (.top i) := by
  cases a with
  | top i => exact ⟨i, Perm.SameCycle.rfl⟩
  | bottom i => exact Fin.elim0 i
  | hub h i => exact ⟨i, Perm.SameCycle.rfl.apply_right⟩
  | joint j side => exact j.elim

theorem circuitStep_up_to_bottom (P : InvolutionPresentation R S) (r : R) (a : (up P r).Dart) :
    ∃ i, (up P r).circuitStep.SameCycle a (.bottom i) := by
  cases a with
  | top i => exact Fin.elim0 i
  | bottom i => exact ⟨i, Perm.SameCycle.rfl⟩
  | hub h i => exact ⟨i, Perm.SameCycle.rfl.apply_right⟩
  | joint j side => exact j.elim

theorem circuitStep_down_sameCycle (P : InvolutionPresentation R S) (r : R) (a b : (down P r).Dart) :
    (down P r).circuitStep.SameCycle a b := by
  obtain ⟨i, hi⟩ := circuitStep_down_to_top P r a
  obtain ⟨j, hj⟩ := circuitStep_down_to_top P r b
  apply hi.trans (Perm.SameCycle.trans ?_ hj.symm)
  apply ((down P r).circuit_eq_iff _ _).mp
  apply ((down P r).boundaryNext_sameCycle_iff (.inl i) (.inl j)).mp
  apply (FiniteReturn.sameCycle_congr _ _ (boundaryOrderIndex (P.word r) [])
    (down P r).numberedBoundaryNext_index _ _).mpr
  rw [numberedBoundaryNext_down]
  exact finRotate_sameCycle _ _

theorem circuitStep_up_sameCycle (P : InvolutionPresentation R S) (r : R) (a b : (up P r).Dart) :
    (up P r).circuitStep.SameCycle a b := by
  obtain ⟨i, hi⟩ := circuitStep_up_to_bottom P r a
  obtain ⟨j, hj⟩ := circuitStep_up_to_bottom P r b
  apply hi.trans (Perm.SameCycle.trans ?_ hj.symm)
  apply ((up P r).circuit_eq_iff _ _).mp
  apply ((up P r).boundaryNext_sameCycle_iff (.inr i) (.inr j)).mp
  apply (FiniteReturn.sameCycle_congr _ _ (boundaryOrderIndex [] (P.word r))
    (up P r).numberedBoundaryNext_index _ _).mpr
  rw [numberedBoundaryNext_up]
  exact finRotate_sameCycle _ _

theorem eulerDefect_down (P : InvolutionPresentation R S) (r : R) :
    eulerDefect (down P r).pairing.perm (down P r).circuitStep = 0 := by
  by_cases hn : 0 < (P.word r).length
  · have hc := orbit_card_of_one_cycle (down P r).circuitStep (.top ⟨0, hn⟩)
      (circuitStep_down_sameCycle P r)
    have hk := component_card_of_one_cycle (down P r).pairing.perm (down P r).circuitStep
      (.top ⟨0, hn⟩) (circuitStep_down_sameCycle P r)
    have hv : Nat.card (down P r).Vertex = (P.word r).length + 1 := by
      rw [Nat.card_eq_fintype_card, vertex_card]
      simp only [← Nat.card_eq_fintype_card]
      change (P.word r).length + 0 + (Nat.card Unit + Nat.card Empty) = _
      simp
    have he : Nat.card (down P r).Edge = (P.word r).length := by
      have hd := (down P r).degree_sum
      change (P.word r).length + 0 +
        ((∑ _ : Unit, (P.word r).length) + 2 * Fintype.card Empty) = 2 * Fintype.card (down P r).Edge at hd
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hd
      simp only [Nat.card_unique, Nat.card_eq_fintype_card (α := Empty), Fintype.card_empty,
        one_mul, mul_zero, add_zero] at hd
      omega
    unfold eulerDefect
    rw [eulerCount_eq_ribbonEuler _ (fun _ => hn), hk]
    unfold ribbonEuler
    simp only [← Nat.card_eq_fintype_card]
    change (Nat.card (down P r).Vertex : Int) - Nat.card (down P r).Edge +
      Nat.card (Orbit (down P r).circuitStep) - 2 * (1 : Nat) = 0
    rw [hc, hv, he]
    omega
  · let : IsEmpty (down P r).Dart := ⟨by
      intro a
      obtain ⟨i, _⟩ := circuitStep_down_to_top P r a
      have hi := i.isLt
      omega⟩
    exact eulerDefect_of_empty _ _

theorem eulerDefect_up (P : InvolutionPresentation R S) (r : R) :
    eulerDefect (up P r).pairing.perm (up P r).circuitStep = 0 := by
  by_cases hn : 0 < (P.word r).length
  · have hc := orbit_card_of_one_cycle (up P r).circuitStep (.bottom ⟨0, hn⟩)
      (circuitStep_up_sameCycle P r)
    have hk := component_card_of_one_cycle (up P r).pairing.perm (up P r).circuitStep
      (.bottom ⟨0, hn⟩) (circuitStep_up_sameCycle P r)
    have hv : Nat.card (up P r).Vertex = (P.word r).length + 1 := by
      rw [Nat.card_eq_fintype_card, vertex_card]
      simp only [← Nat.card_eq_fintype_card]
      change 0 + (P.word r).length + (Nat.card Unit + Nat.card Empty) = _
      simp
    have he : Nat.card (up P r).Edge = (P.word r).length := by
      have hd := (up P r).degree_sum
      change 0 + (P.word r).length +
        ((∑ _ : Unit, (P.word r).length) + 2 * Fintype.card Empty) = 2 * Fintype.card (up P r).Edge at hd
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hd
      simp only [Nat.card_unique, Nat.card_eq_fintype_card (α := Empty), Fintype.card_empty,
        one_mul, mul_zero, add_zero, zero_add] at hd
      omega
    unfold eulerDefect
    rw [eulerCount_eq_ribbonEuler _ (fun _ => hn), hk]
    unfold ribbonEuler
    simp only [← Nat.card_eq_fintype_card]
    change (Nat.card (up P r).Vertex : Int) - Nat.card (up P r).Edge +
      Nat.card (Orbit (up P r).circuitStep) - 2 * (1 : Nat) = 0
    rw [hc, hv, he]
    omega
  · let : IsEmpty (up P r).Dart := ⟨by
      intro a
      obtain ⟨i, _⟩ := circuitStep_up_to_bottom P r a
      have hi := i.isLt
      omega⟩
    exact eulerDefect_of_empty _ _

end PortGraph
end ThomGame.Pictures
