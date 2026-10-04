module

public import ThomGame.Pictures.LoopCutEuler
public import ThomGame.Pictures.MatchingDiagram
public import ThomGame.Pictures.FinCirclePaths
public import ThomGame.Pictures.SelectedSmoothingStep

/-!
# Euler saturation forces a circular matching to be noncrossing

An alternating pair of chords would reconnect the two dual components
created by cutting either chord. The loop-cut Euler theorem forbids this.
Together with matching realization, this constructs a vertex-free diagram
from the finite Euler condition, without a geometric embedding premise.
-/

@[expose] public section
namespace ThomGame.Pictures

open Equiv CycleSurgery RibbonConnectivity CircularPartition MarkedReturn
open scoped Classical

namespace FinCircle

variable {n : Nat}

theorem hit_before_cut {a b c : Fin n} (hs : sbtw a b c) :
    Hit (finRotate n) (fun x => x = a ∨ x = c) a b := by
  let : NeZero n := a.neZero
  rcases Fin.sbtw_iff.mp hs with ⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩
  · apply hit_of_lt _ a b hab
    rintro x hax hxb (rfl | rfl) <;> omega
  · apply hit_wrap
    · rintro x hax (rfl | rfl) <;> omega
    · rintro x hxb (rfl | rfl) <;> omega
  · apply hit_of_lt _ a b hab
    rintro x hax hxb (rfl | rfl) <;> omega

theorem splice_sameCycle_of_sbtw {a b c : Fin n} (hs : sbtw a b c) :
    (splice (finRotate n) a c).SameCycle a b := by
  have hba : b ≠ a := by intro he; subst b; simp only [Fin.sbtw_iff] at hs; omega
  have hbc : b ≠ c := by intro he; subst b; simp only [Fin.sbtw_iff] at hs; omega
  have hpath := (hit_before_cut hs).twist_targets (swap a c) (by
    intro x hx
    exact swap_apply_of_ne_of_ne (fun he => hx (Or.inl he)) (fun he => hx (Or.inr he)))
  change Hit (splice (finRotate n) a c) (fun x => x = a ∨ x = c) a (swap a c b) at hpath
  rw [swap_apply_of_ne_of_ne hba hbc] at hpath
  exact hpath.sameCycle

end FinCircle

namespace RotationEuler

variable {n : Nat} (t : Perm (Fin n)) (ht : Function.Involutive t)

include ht in
/-- Fixed ports are allowed, as they arise in edge contraction traces. -/
theorem circular_noninterlacing
    (hEuler : count (finRotate n) t = 2 * Nat.card (Component (finRotate n) t)) :
    NonInterlacing sbtw t := by
  intro a b c d habc hacd hac hbd
  have hca : c = t a := by
    rcases (involutive_sameCycle t ht a c).mp hac with he | he
    · subst c
      exact (sbtw_irrefl_left_right habc).elim
    · exact he
  have hdb : d = t b := by
    rcases (involutive_sameCycle t ht b d).mp hbd with he | he
    · subst d
      exact (habc.not_sbtw hacd.cyclic_left).elim
    · exact he
  have hda : d ≠ a := by
    intro he
    have hh := hacd
    rw [he] at hh
    exact sbtw_irrefl_left_right hh
  have hdc : d ≠ c := by
    intro he
    have hh := hacd
    rw [he] at hh
    simp only [Fin.sbtw_iff] at hh
    omega
  have hne : a ≠ t a := by
    intro he
    have hh := habc
    rw [hca, ← he] at hh
    exact sbtw_irrefl_left_right hh
  let t₀ := CycleSurgery.splice t a (t a)
  let f := t * finRotate n
  have hprod : t₀ * f = CycleSurgery.splice (finRotate n) a c := by
    rw [hca]
    exact cutLoop_product (finRotate n) t ht a
  have hab : Connected f t₀ a b := by
    apply RotationEuler.sameCycle_mul_connected
    rw [hprod]
    exact FinCircle.splice_sameCycle_of_sbtw habc
  have hcd : Connected f t₀ c d := by
    apply RotationEuler.sameCycle_mul_connected
    rw [hprod]
    simpa only [CycleSurgery.splice, swap_comm a c] using
      FinCircle.splice_sameCycle_of_sbtw hacd.cyclic_left
  have hstep : t₀ b = d := by
    change swap a (t a) (t b) = d
    rw [← hdb, ← hca, swap_apply_of_ne_of_ne hda hdc]
  have hmid : Connected f t₀ b d := by
    have hh : Connected f t₀ b (t₀ b) := Connected.circuit b
    rwa [hstep] at hh
  have hconnect : Connected f t₀ a (t a) := by
    simpa only [hca] using hab.trans (hmid.trans hcd.symm)
  exact (cutLoop_separates (finRotate n) t ht hEuler a hne
    (PortGraph.finRotate_sameCycle a (t a)) hconnect).elim

end RotationEuler

namespace Pairing

variable {S : Type*} {n : Nat} {label : Fin n → S} (p : Pairing label)

theorem noninterlacing_of_euler
    (hEuler : RotationEuler.count (finRotate n) p.perm =
      2 * Nat.card (Component (finRotate n) p.perm)) :
    NonInterlacing sbtw p.perm :=
  RotationEuler.circular_noninterlacing p.perm p.involutive hEuler

end Pairing

theorem exists_matching_diagram_of_euler {R S : Type*} (P : InvolutionPresentation R S)
    {n : Nat} (label : Fin n → S) (p : Pairing label)
    (hEuler : RotationEuler.count (finRotate n) p.perm =
      2 * Nat.card (Component (finRotate n) p.perm)) :
    ∃ d : Diagram P (List.ofFn label) [], d.labels = [] :=
  exists_matching_diagram P label p (p.noninterlacing_of_euler hEuler)

end ThomGame.Pictures
