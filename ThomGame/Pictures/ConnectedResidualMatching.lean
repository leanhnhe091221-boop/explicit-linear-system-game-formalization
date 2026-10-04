module

public import ThomGame.Pictures.EdgeContractionTrace
public import ThomGame.Pictures.ResidualMatching
public import ThomGame.Pictures.OrbitEnumeration
public import ThomGame.Pictures.ComponentTransport

/-!
# The residual matching of a connected contraction trace

The terminal vertex orbit is enumerated by its actual finite iterates.
Conjugating the remaining edge involution by that enumeration gives an
Euler-saturating circular partial matching. Deleting its fixed ports
therefore gives an ordered boundary with a relation-free diagram.
Assembling the contracted relation blocks is still a separate step.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv FiniteReturn RibbonConnectivity

namespace RotationEuler

variable {A B : Type*} [Finite A] [Finite B]

theorem count_congr (r t : Perm A) (r' t' : Perm B) (e : A ≃ B)
    (hr : ∀ x, r' (e x) = e (r x)) (ht : ∀ x, t' (e x) = e (t x)) :
    count r t = count r' t' := by
  have hp : ∀ x, (t' * r') (e x) = e ((t * r) x) := by
    intro x
    simp only [Perm.mul_apply, hr, ht]
  unfold count
  rw [Nat.card_congr (orbitEquiv r r' e hr), Nat.card_congr (orbitEquiv t t' e ht),
    Nat.card_congr (orbitEquiv (t * r) (t' * r') e hp), Nat.card_congr e]

end RotationEuler

namespace EdgeContraction

variable {D : Type*} [DecidableEq D] [Finite D]
    {r t r' t' : Perm D} {k : Nat} (c : EdgeContraction r t r' t' k)
    (hterm : ∀ a, r'.SameCycle a (t' a)) (hconn : ∀ x y, Connected r t x y) (a : D)

noncomputable def terminalEnumeration : Fin (OrbitEnumeration.length r' a) ≃ D :=
  Equiv.ofBijective (OrbitEnumeration.dart r' a)
    ⟨(OrbitEnumeration.dart r' a).injective, fun b =>
      (OrbitEnumeration.dart_range r' a b).mpr
        ((c.terminal_original_connected hterm a b).mpr (hconn a b))⟩

theorem terminalEnumeration_rotation (i : Fin (OrbitEnumeration.length r' a)) :
    terminalEnumeration c hterm hconn a (finRotate _ i) =
      r' (terminalEnumeration c hterm hconn a i) :=
  OrbitEnumeration.dart_next r' a i

noncomputable def terminalEdge : Perm (Fin (OrbitEnumeration.length r' a)) :=
  ((terminalEnumeration c hterm hconn a).trans t').trans
    (terminalEnumeration c hterm hconn a).symm

theorem terminalEdge_step (i : Fin (OrbitEnumeration.length r' a)) :
    terminalEnumeration c hterm hconn a (terminalEdge c hterm hconn a i) =
      t' (terminalEnumeration c hterm hconn a i) :=
  (terminalEnumeration c hterm hconn a).apply_symm_apply _

theorem terminalEdge_involutive (ht : Function.Involutive t) :
    Function.Involutive (terminalEdge c hterm hconn a) := by
  intro i
  apply (terminalEnumeration c hterm hconn a).injective
  rw [terminalEdge_step, terminalEdge_step, c.involutive ht]

theorem terminalEdge_label {S : Type*} (ht : Function.Involutive t)
    (label : D → S) (hl : ∀ x, label (t x) = label x)
    (i : Fin (OrbitEnumeration.length r' a)) :
    label (terminalEnumeration c hterm hconn a (terminalEdge c hterm hconn a i)) =
      label (terminalEnumeration c hterm hconn a i) := by
  rw [terminalEdge_step]
  exact c.preserves_label ht label hl _

theorem terminalEdge_saturated (ht : Function.Involutive t)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    RotationEuler.count (finRotate _) (terminalEdge c hterm hconn a) =
      2 * Nat.card (Component (finRotate _) (terminalEdge c hterm hconn a)) := by
  let e := terminalEnumeration c hterm hconn a
  have hr : ∀ i, r' (e i) = e (finRotate _ i) :=
    fun i => (terminalEnumeration_rotation c hterm hconn a i).symm
  have he : ∀ i, t' (e i) = e (terminalEdge c hterm hconn a i) :=
    fun i => (terminalEdge_step c hterm hconn a i).symm
  rw [RotationEuler.count_congr _ _ r' t' e hr he,
    Nat.card_congr (componentCongrEquiv _ _ r' t' e hr he)]
  exact c.saturated ht hEuler

noncomputable def residualWord {S : Type*} (label : D → S) : List S :=
  ResidualMatching.word (terminalEdge c hterm hconn a)
    (fun i => label (terminalEnumeration c hterm hconn a i))

theorem exists_residual_diagram {R S : Type*} (P : InvolutionPresentation R S)
    (ht : Function.Involutive t) (label : D → S) (hl : ∀ x, label (t x) = label x)
    (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    ∃ d : Diagram P (residualWord c hterm hconn a label) [], d.labels = [] :=
  ResidualMatching.exists_diagram_of_euler _ (terminalEdge_involutive c hterm hconn a ht)
    _ (terminalEdge_label c hterm hconn a ht label hl) P
    (terminalEdge_saturated c hterm hconn a ht hEuler)

end EdgeContraction
end ThomGame.Pictures
