module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Semisimplicity of Artinian C-star rings

A self-adjoint nilpotent element has zero norm. For an element of the
Jacobson radical, its star-square is again in the radical by left-ideal
closure. Nilpotence of the radical and the C-star identity then force
the original element to vanish. No star-invariance of the radical is
assumed, and no completeness is needed.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

theorem cstarSelfAdjoint_eq_zero_of_isNilpotent {x : E}
    (hx : IsSelfAdjoint x) (hnil : IsNilpotent x) : x = 0 := by
  obtain ⟨n, hn⟩ := hnil
  have hp : x ^ (2 ^ n) = 0 := pow_eq_zero_of_le (Nat.lt_two_pow_self.le) hn
  have hnorm : ‖x‖ ^ (2 ^ n) = 0 := by
    rw [← hx.norm_pow_two_pow n, hp, norm_zero]
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm)

theorem cstarArtinian_jacobson_eq_bot [IsArtinianRing E] : Ring.jacobson E = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hsq : star x * x ∈ Ring.jacobson E := (Ring.jacobson E).mul_mem_left (star x) hx
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := E)
  have hpow := Ideal.pow_mem_pow hsq n
  rw [hn] at hpow
  have hzero : star x * x = 0 :=
    cstarSelfAdjoint_eq_zero_of_isNilpotent (IsSelfAdjoint.star_mul_self x)
      ⟨n, (Ideal.mem_bot.mp hpow)⟩
  exact Ideal.mem_bot.mpr (star_mul_self_eq_zero.mp hzero)

theorem cstarArtinian_isSemisimpleRing [IsArtinianRing E] : IsSemisimpleRing E :=
  IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr cstarArtinian_jacobson_eq_bot

end ThomGame.Analysis
