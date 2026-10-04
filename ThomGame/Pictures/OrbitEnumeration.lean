module

public import ThomGame.Pictures.PermutationSurgery
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Indexed enumeration of one orbit of a finite permutation -/

@[expose] public section
namespace ThomGame.Pictures.OrbitEnumeration

variable {D : Type*} [Finite D] (f : Equiv.Perm D) (a : D)

noncomputable def length : Nat := Function.minimalPeriod f a

theorem length_pos : 0 < length f a := CycleSurgery.period_pos f a

instance : NeZero (length f a) := ⟨Nat.ne_of_gt (length_pos f a)⟩

noncomputable def dart : Fin (length f a) ↪ D where
  toFun i := (f ^ i.val) a
  inj' i j hij := Fin.ext (CycleSurgery.pow_injective_before_period f a i.isLt j.isLt hij)

theorem dart_zero : dart f a 0 = a := rfl

omit [Finite D] in
theorem dart_sameCycle (i : Fin (length f a)) : f.SameCycle a (dart f a i) :=
  ⟨(i.val : Int), by rw [zpow_natCast]; rfl⟩

theorem dart_range (b : D) : b ∈ Set.range (dart f a) ↔ f.SameCycle a b := by
  constructor
  · rintro ⟨i, rfl⟩
    exact dart_sameCycle f a i
  · intro h
    obtain ⟨n, hn, he⟩ := CycleSurgery.exists_pow_before_period f h
    exact ⟨⟨n, hn⟩, he⟩

omit [Finite D] in
theorem dart_next (i : Fin (length f a)) :
    dart f a (finRotate (length f a) i) = f (dart f a i) := by
  change (f ^ (finRotate (length f a) i).val) a = f ((f ^ i.val) a)
  rw [finRotate_apply]
  change (f ^ ((i.val + 1 % length f a) % length f a)) a = f ((f ^ i.val) a)
  rw [Nat.add_mod_mod]
  exact Function.iterate_mod_minimalPeriod_eq.trans (CycleSurgery.apply_pow f a i.val).symm

end ThomGame.Pictures.OrbitEnumeration
