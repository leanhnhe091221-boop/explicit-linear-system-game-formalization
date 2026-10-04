module

public import ThomGame.Pictures.CircularPartition
public import ThomGame.Pictures.GraphRotation
public import Mathlib.Data.Fin.Rev

/-! # Orbits of involutions and the noncrossing reflection matching -/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open MarkedReturn

variable {A : Type*} [Finite A]

theorem involutive_sameCycle (f : Equiv.Perm A) (hf : Function.Involutive f) (x y : A) :
    f.SameCycle x y ↔ y = x ∨ y = f x := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with he | he
      · exact Or.inr (congrArg f he)
      · exact Or.inl ((congrArg f he).trans (hf x))
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact Equiv.Perm.SameCycle.rfl.apply_right

/-- A one- or two-point orbit has a unique cyclic orientation. -/
theorem follows_involution (c f : Equiv.Perm A) (hf : Function.Involutive f)
    (hc : ∀ x y, c.SameCycle x y) : Follows c f := by
  intro x y hxy
  let O := fun a => f.SameCycle x a
  let y' : Subtype O := ⟨y, hxy⟩
  let z' : Subtype O := ⟨f y, hxy.apply_right⟩
  have hz : (perm c O y').val = f y := by
    have hym : f.SameCycle y (perm c O y').val := hxy.symm.trans (perm c O y').property
    rcases (involutive_sameCycle f hf y _).mp hym with he | he
    · by_cases hy : f y = y
      · exact he.trans hy.symm
      · have hr : (perm c O).SameCycle y' z' := (sameCycle_iff c O y' z').mpr (hc _ _)
        have hfixed : perm c O y' = y' := Subtype.ext he
        have hsame := hr.eq_of_left hfixed
        have hval : y = f y := congrArg Subtype.val hsame
        exact (hy hval.symm).elim
    · exact he
  have hr := hit_perm c O y'
  rw [hz] at hr
  exact hr

theorem reflection_noninterlacing (n : Nat) :
    NonInterlacing (sbtw : Fin n → Fin n → Fin n → Prop) Fin.revPerm := by
  intro a b c d habc hacd hac hbd
  have hc : c = a.rev := by
    rcases (involutive_sameCycle Fin.revPerm Fin.rev_involutive a c).mp hac with he | he
    · subst c
      exact (sbtw_irrefl_left_right habc).elim
    · exact he
  have hd : d = b.rev := by
    rcases (involutive_sameCycle Fin.revPerm Fin.rev_involutive b d).mp hbd with he | he
    · subst d
      exact (habc.not_sbtw hacd.cyclic_left).elim
    · exact he
  subst c
  subst d
  simp only [Fin.sbtw_iff, Fin.lt_def, Fin.val_rev] at habc hacd
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem reflection_orderedNoncrossing (n : Nat) :
    OrderedNoncrossing (finRotate n) (sbtw : Fin n → Fin n → Fin n → Prop) Fin.revPerm :=
  ⟨follows_involution _ _ Fin.rev_involutive (PortGraph.finRotate_sameCycle),
    reflection_noninterlacing n⟩

theorem rotation_orderedNoncrossing (n : Nat) :
    OrderedNoncrossing (finRotate n) (sbtw : Fin n → Fin n → Fin n → Prop) (finRotate n) :=
  ⟨follows_self _, noninterlacing_of_one_orbit _ _ (PortGraph.finRotate_sameCycle)⟩

end ThomGame.Pictures.CircularPartition
