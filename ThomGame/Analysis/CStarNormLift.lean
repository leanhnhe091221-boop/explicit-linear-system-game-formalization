module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Norm-controlled lifts through a star algebra homomorphism

Continuous functional calculus clips self-adjoint lifts without changing
their images when the image already satisfies the requested norm bound.
Real and imaginary parts then give lifts of arbitrary elements with a
uniform factor two in the norm bound. Surjectivity is not assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped CStarAlgebra

def realNormClamp (K t : ℝ) : ℝ := max (-K) (min K t)

theorem realNormClamp_continuous (K : ℝ) : Continuous (realNormClamp K) := by
  unfold realNormClamp
  fun_prop

theorem realNormClamp_norm_le (K : ℝ) (hK : 0 ≤ K) (t : ℝ) : ‖realNormClamp K t‖ ≤ K := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem realNormClamp_eq_self (K t : ℝ) (ht : ‖t‖ ≤ K) : realNormClamp K t = t := by
  rw [Real.norm_eq_abs, abs_le] at ht
  exact (congrArg (max (-K)) (min_eq_right ht.2)).trans (max_eq_right ht.1)

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

noncomputable def cstarNormClamp (K : ℝ) (a : A) : A := cfc (realNormClamp K) a

theorem cstarNormClamp_selfAdjoint (K : ℝ) (a : A) : IsSelfAdjoint (cstarNormClamp K a) :=
  IsSelfAdjoint.cfc

theorem cstarNormClamp_norm_le (K : ℝ) (hK : 0 ≤ K) (a : A) : ‖cstarNormClamp K a‖ ≤ K :=
  norm_cfc_le hK (fun t _ => realNormClamp_norm_le K hK t)

theorem cstarNormClamp_eq_self (K : ℝ) (a : A) (ha : IsSelfAdjoint a) (hbound : ‖a‖ ≤ K) :
    cstarNormClamp K a = a := by
  change cfc (realNormClamp K) a = a
  calc
    cfc (realNormClamp K) a = cfc (fun t : ℝ => t) a := by
      apply cfc_congr
      intro t ht
      exact realNormClamp_eq_self K t
        ((IsometricContinuousFunctionalCalculus.norm_spectrum_le a ht ha).trans hbound)
    _ = a := cfc_id' ℝ a ha

theorem map_cstarNormClamp (φ : A →⋆ₐ[ℂ] B) (K : ℝ) (a : A) (ha : IsSelfAdjoint a) :
    φ (cstarNormClamp K a) = cstarNormClamp K (φ a) :=
  φ.map_cfc (realNormClamp K) a (realNormClamp_continuous K).continuousOn
    (map_continuous φ) ha (ha.map φ)

theorem exists_selfAdjoint_norm_lift (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : IsSelfAdjoint a)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖φ a‖ ≤ K) :
    ∃ b : A, IsSelfAdjoint b ∧ ‖b‖ ≤ K ∧ φ b = φ a := by
  refine ⟨cstarNormClamp K a, cstarNormClamp_selfAdjoint K a, cstarNormClamp_norm_le K hK a, ?_⟩
  rw [map_cstarNormClamp φ K a ha, cstarNormClamp_eq_self K (φ a) (ha.map φ) hbound]

theorem exists_cstar_norm_lift (φ : A →⋆ₐ[ℂ] B) (a : A) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ‖φ a‖ ≤ K) : ∃ b : A, ‖b‖ ≤ 2 * K ∧ φ b = φ a := by
  have hre : ‖φ (realPart a : A)‖ ≤ K := by
    rw [map_realPart]
    exact (realPart.norm_le (φ a)).trans hbound
  have him : ‖φ (imaginaryPart a : A)‖ ≤ K := by
    rw [map_imaginaryPart]
    exact (imaginaryPart.norm_le (φ a)).trans hbound
  obtain ⟨r, _, hr, her⟩ := exists_selfAdjoint_norm_lift φ (realPart a) (realPart a).property K hK hre
  obtain ⟨s, _, hs, hes⟩ := exists_selfAdjoint_norm_lift φ (imaginaryPart a) (imaginaryPart a).property K hK him
  refine ⟨r + Complex.I • s, ?_, ?_⟩
  · calc
      ‖r + Complex.I • s‖ ≤ ‖r‖ + ‖Complex.I • s‖ := norm_add_le _ _
      _ = ‖r‖ + ‖s‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ 2 * K := by linarith
  · rw [map_add, map_smul, her, hes, map_realPart, map_imaginaryPart,
      realPart_add_I_smul_imaginaryPart]

end ThomGame.Analysis
