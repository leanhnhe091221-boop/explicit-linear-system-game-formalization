module

public import ThomGame.Pictures.DiagramGraph
public import ThomGame.Pictures.DiagramCharge
public import ThomGame.Pictures.SmoothingTrace
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Mod-two charge conservation for arbitrary port graphs

Every edge contributes two equal charges. Splitting the complete dart set
into boundary ports, relation ports, and subdivision ports yields the
boundary charge formula without a planarity or diagram-syntax assumption.
-/

@[expose] public section
namespace ThomGame.Pictures

open scoped BigOperators
open InvolutionDerivation

theorem Pairing.sum_charge {A S : Type*} [Fintype A] {label : A → S}
    (p : Pairing label) (χ : S → ZMod 2) : (∑ a, χ (label a)) = 0 := by
  classical
  exact Finset.sum_ninvolution p.twin
    (fun a => by rw [p.label_twin]; exact parity_self_add _)
    (fun a _ => p.ne_self a) (fun _ => Finset.mem_univ _) p.involutive

namespace PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

theorem charge_balance (χ : S → ZMod 2) :
    (∑ h : G.Hub, ((P.word (G.hubLabel h)).map χ).sum) =
      (u.map χ).sum + (v.map χ).sum := by
  classical
  have hd := G.pairing.sum_charge χ
  rw [← Port.sumEquiv.sum_comp] at hd
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type,
    Port.sumEquiv, Equiv.coe_fn_mk, Port.label, Fintype.sum_bool,
    parity_self_add, Finset.sum_const_zero, add_zero] at hd
  change (∑ i : Fin u.length, χ u[i.val]) + (∑ i : Fin v.length, χ v[i.val]) +
    (∑ h : G.Hub, ∑ i : Fin (P.word (G.hubLabel h)).length,
      χ (P.word (G.hubLabel h))[i.val]) = 0 at hd
  simp only [Fin.sum_univ_fun_getElem] at hd
  apply add_left_cancel (a := (u.map χ).sum + (v.map χ).sum)
  rw [hd, parity_self_add]

/-- The parity of the number of relation vertices with a given label. -/
noncomputable def character (r : R) : ZMod 2 := by
  classical
  exact (Nat.card {h : G.Hub // G.hubLabel h = r} : ZMod 2)

theorem character_eq_sum [DecidableEq R] (r : R) :
    G.character r = ∑ h : G.Hub, if G.hubLabel h = r then (1 : ZMod 2) else 0 := by
  classical
  simp [character, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sign_eq_character [Fintype R] : G.sign = ∑ r, G.character r * P.parity r := by
  classical
  simp_rw [G.character_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [sign, ite_mul]

end PortGraph

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

theorem Diagram.graph_character [DecidableEq R] (d : Diagram P u v) (r : R) :
    d.graph.character r = d.character r := by
  rw [PortGraph.character_eq_sum]
  simp_rw [d.hubLabel_index]
  change (∑ h, (fun i : Fin d.labels.length =>
    if d.labels[i.val] = r then (1 : ZMod 2) else 0) (d.hubIndex h)) = _
  rw [d.hubIndex.sum_comp (fun i : Fin d.labels.length =>
    if d.labels[i.val] = r then (1 : ZMod 2) else 0),
    Fin.sum_univ_fun_getElem d.labels (fun a : R => if a = r then (1 : ZMod 2) else 0),
    sum_indicator_eq_count]
  rfl

theorem Smoothing.character {G H : PortGraph P u v} {circles : List S}
    (h : Smoothing G H circles) (r : R) : H.character r = G.character r := by
  induction h with
  | refl _ => rfl
  | step j tail ih => exact ih

end ThomGame.Pictures
