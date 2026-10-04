module

public import ThomGame.Pictures.VerticalNoncrossing
public import ThomGame.Pictures.GraphBoundaryComponents
public import Mathlib.Logic.Equiv.Sum

/-!
# Actual partial seam permutations on all graph darts

Only the first `k` matching boundary pairs have their targets exchanged.
Internal darts are retained throughout. The remaining marked darts are
the outer boundary together with the unprocessed seam pairs.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv MarkedReturn CycleSurgery RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v w : List S}
variable (G : PortGraph P u v) (H : PortGraph P v w)

def partialDartSwap (k : Nat) : Perm (G.Dart ⊕ H.Dart) where
  toFun
    | .inl (.bottom i) => if i.val < k then .inr (.top i) else .inl (.bottom i)
    | .inr (.top i) => if i.val < k then .inl (.bottom i) else .inr (.top i)
    | x => x
  invFun
    | .inl (.bottom i) => if i.val < k then .inr (.top i) else .inl (.bottom i)
    | .inr (.top i) => if i.val < k then .inl (.bottom i) else .inr (.top i)
    | x => x
  left_inv x := by
    rcases x with a | a <;> cases a <;> first | rfl | (rename_i i; by_cases hi : i.val < k <;> simp [hi])
  right_inv x := by
    rcases x with a | a <;> cases a <;> first | rfl | (rename_i i; by_cases hi : i.val < k <;> simp [hi])

theorem partialDartSwap_zero : partialDartSwap G H 0 = 1 := by
  ext x
  rcases x with a | a <;> cases a <;> simp [partialDartSwap]

theorem partialDartSwap_all : partialDartSwap G H v.length = seamSwap G H := by
  ext x
  rcases x with a | a <;> cases a <;> simp [partialDartSwap, seamSwap]

theorem partialDartSwap_step (i : Fin v.length) :
    partialDartSwap G H (i.val + 1) =
      swap (.inl (.bottom i)) (.inr (.top i)) * partialDartSwap G H i.val := by
  ext x
  rcases x with a | a <;> cases a
  all_goals first | (solve | simp [partialDartSwap, swap_apply_def]) | skip
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp [partialDartSwap]
    · have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
      simp only [Perm.mul_apply, partialDartSwap, Equiv.coe_fn_mk]
      by_cases hj : j.val < i.val
      · simp [hj, show j.val < i.val + 1 by omega, swap_apply_def, hji]
      · simp [hj, show ¬ j.val < i.val + 1 by omega, swap_apply_def, hji]

def FullSeamRemaining (k : Nat) : G.Dart ⊕ H.Dart → Prop
  | .inl (.top _) => True
  | .inl (.bottom i) => k ≤ i.val
  | .inr (.top i) => k ≤ i.val
  | .inr (.bottom _) => True
  | _ => False

theorem fullSeamRemaining_boundary (k : Nat) (x : G.Dart ⊕ H.Dart) (hx : FullSeamRemaining G H k x) :
    Sum.elim G.IsBoundary H.IsBoundary x := by
  rcases x with a | a <;> cases a <;> trivial

theorem fullSeamRemaining_zero (x : G.Dart ⊕ H.Dart) :
    FullSeamRemaining G H 0 x ↔ Sum.elim G.IsBoundary H.IsBoundary x := by
  rcases x with a | a <;> cases a <;> simp [FullSeamRemaining, IsBoundary]

theorem fullSeamRemaining_mono (k : Nat) (x : G.Dart ⊕ H.Dart)
    (hx : FullSeamRemaining G H (k + 1) x) : FullSeamRemaining G H k x := by
  rcases x with a | a <;> cases a <;> simp only [FullSeamRemaining] at hx ⊢ <;> omega

theorem fullSeamRemaining_all (x : G.Dart ⊕ H.Dart) :
    FullSeamRemaining G H v.length x ↔ (G.comp H).IsBoundary (compPorts G H x) := by
  rcases x with a | a <;> cases a <;> simp [FullSeamRemaining, IsBoundary, compPorts]

theorem fullSeamRemaining_index (k : Nat) (b : SeamBoundary u v w) :
    FullSeamRemaining G H k (oldBoundaryDart G H b) ↔ SeamRemaining u v w k b := by
  rcases b with (i | i) | (i | i) <;> rfl

theorem partialDartSwap_fixed_remaining (k : Nat) (x : G.Dart ⊕ H.Dart)
    (hx : FullSeamRemaining G H k x) : partialDartSwap G H k x = x := by
  rcases x with a | a <;> cases a <;>
    simp_all [FullSeamRemaining, partialDartSwap]

theorem partialDartSwap_fixed_off_boundary (k : Nat) (x : G.Dart ⊕ H.Dart)
    (hx : ¬ Sum.elim G.IsBoundary H.IsBoundary x) : partialDartSwap G H k x = x := by
  rcases x with a | a <;> cases a <;> first | rfl | exact (hx trivial).elim

theorem partialDartSwap_oldBoundary (k : Nat) (b : SeamBoundary u v w) :
    partialDartSwap G H k (oldBoundaryDart G H b) =
      oldBoundaryDart G H (partialBoundarySwap u v w k b) := by
  rcases b with (i | i) | (i | i) <;> by_cases hi : i.val < k <;>
    simp [partialDartSwap, partialBoundarySwap, oldBoundaryDart, boundaryDart, boundaryPorts, hi]

noncomputable def fullPartialSeam (k : Nat) : Perm (G.Dart ⊕ H.Dart) :=
  partialDartSwap G H k * Equiv.sumCongr G.circuitStep H.circuitStep

noncomputable def boundaryPartialSeam (k : Nat) : Perm (SeamBoundary u v w) :=
  partialBoundarySwap u v w k * Equiv.sumCongr G.boundaryNext H.boundaryNext

theorem fullPartialSeam_zero : fullPartialSeam G H 0 = Equiv.sumCongr G.circuitStep H.circuitStep := by
  rw [fullPartialSeam, partialDartSwap_zero, one_mul]

theorem fullPartialSeam_step (i : Fin v.length) :
    fullPartialSeam G H (i.val + 1) = splice (fullPartialSeam G H i.val)
      (.inl (.bottom i)) (.inr (.top i)) := by
  rw [fullPartialSeam, partialDartSwap_step]
  simp only [fullPartialSeam, splice, mul_assoc]

theorem fullPartialSeam_all (x : G.Dart ⊕ H.Dart) :
    (G.comp H).circuitStep (compPorts G H x) = compPorts G H (fullPartialSeam G H v.length x) := by
  rw [circuitStep_compPorts]
  simp only [fullPartialSeam, partialDartSwap_all, Perm.mul_apply]
  rfl

theorem fullPartialSeam_leaves (k : Nat) :
    Leaves (Equiv.sumCongr G.pairing.perm H.pairing.perm) (fullPartialSeam G H k)
      (FullSeamRemaining G H k) := by
  intro x hx
  have ho := fullSeamRemaining_boundary G H k x hx
  have he : Equiv.sumCongr G.circuitStep H.circuitStep
      (Equiv.sumCongr G.pairing.perm H.pairing.perm x) = x := by
    rcases x with a | a
    · exact congrArg Sum.inl (G.boundary_leaves a ho)
    · exact congrArg Sum.inr (H.boundary_leaves a ho)
  change partialDartSwap G H k (Equiv.sumCongr G.circuitStep H.circuitStep _) = x
  rw [he]
  exact partialDartSwap_fixed_remaining G H k x hx

theorem fullPartialSeam_boundary_hit (k : Nat) (b : SeamBoundary u v w) :
    Hit (fullPartialSeam G H k) (Sum.elim G.IsBoundary H.IsBoundary)
      (oldBoundaryDart G H b) (oldBoundaryDart G H (boundaryPartialSeam G H k b)) := by
  have ht := (sumBoundary_hit G H b).twist_targets (partialDartSwap G H k)
    (partialDartSwap_fixed_off_boundary G H k)
  rw [partialDartSwap_oldBoundary] at ht
  exact ht

end ThomGame.Pictures.PortGraph
