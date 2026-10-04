module

public import ThomGame.Quantum.ClassicalGameValue
public import ThomGame.Quantum.IncidenceGame

/-! Counting rejected incidences gives classical bounds without enumerating
the (possibly very large) space of local response functions. -/

@[expose] public section
namespace ThomGame.SparseSystem

open scoped BigOperators
open Quantum

variable {R C : Type*} [Fintype R] [Nonempty R] [Fintype C] [LinearOrder C]
  (S : SparseSystem R C)

theorem incidenceGame_deterministic_success (alice : R → Fin 3 → ZMod 2)
    (bob : C → ZMod 2) :
    S.incidenceGame.success (deterministicCorrelation alice bob) =
      (3 * (Fintype.card R : ℝ))⁻¹ *
        ∑ p : R × Fin 3, if S.Accepts p.1 p.2 (alice p.1)
          (bob (S.column p.1 p.2)) then 1 else 0 := by
  classical
  rw [S.incidenceGame_success, Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (alice r)]
  · rw [Finset.sum_eq_single (bob (S.column r i))]
    · simp [deterministicCorrelation]
    · intro b _ hb
      simp [deterministicCorrelation, hb]
    · simp
  · intro a _ ha
    simp [deterministicCorrelation, ha]
  · simp

private theorem sum_le_card_sub_one {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, f i ≤ 1) (i₀ : I) (hzero : f i₀ = 0) :
    ∑ i, f i ≤ (Fintype.card I : ℝ) - 1 := by
  classical
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := f) (Finset.mem_univ i₀)
  have hbound : (∑ i ∈ Finset.univ.erase i₀, f i) ≤
      ∑ _i ∈ Finset.univ.erase i₀, (1 : ℝ) :=
    Finset.sum_le_sum (fun i _ => hf i)
  have hcard : (Finset.univ.erase i₀).card + 1 = Fintype.card I := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i₀)
  have hcard' : ((Finset.univ.erase i₀).card : ℝ) + 1 = Fintype.card I := by
    exact_mod_cast hcard
  simp only [hzero, add_zero] at hsplit
  rw [← hsplit]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard'.symm, add_sub_cancel_right]
    using hbound

theorem incidenceGame_deterministic_le_of_not_perfect
    (alice : R → Fin 3 → ZMod 2) (bob : C → ZMod 2)
    (h : ¬ S.PerfectDeterministic alice bob) :
    S.incidenceGame.success (deterministicCorrelation alice bob) ≤
      1 - (3 * (Fintype.card R : ℝ))⁻¹ := by
  classical
  obtain ⟨r, hr⟩ := not_forall.mp h
  obtain ⟨i, hi⟩ := not_forall.mp hr
  have hsum : (∑ p : R × Fin 3, if S.Accepts p.1 p.2 (alice p.1)
      (bob (S.column p.1 p.2)) then (1 : ℝ) else 0) ≤
      3 * (Fintype.card R : ℝ) - 1 := by
    have hh := sum_le_card_sub_one
      (fun p : R × Fin 3 => if S.Accepts p.1 p.2 (alice p.1)
        (bob (S.column p.1 p.2)) then (1 : ℝ) else 0)
      (by intro p; split <;> norm_num) (r, i) (by simp [hi])
    simpa [Fintype.card_prod, mul_comm] using hh
  have hn : 0 < 3 * (Fintype.card R : ℝ) := by positivity
  rw [S.incidenceGame_deterministic_success]
  calc
    _ ≤ (3 * (Fintype.card R : ℝ))⁻¹ * (3 * Fintype.card R - 1) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = 1 - (3 * (Fintype.card R : ℝ))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hn.ne', mul_one]

theorem incidenceGame_deterministic_eq_of_unique_rejection
    (alice : R → Fin 3 → ZMod 2) (bob : C → ZMod 2) (r₀ : R) (i₀ : Fin 3)
    (h : ∀ r i, S.Accepts r i (alice r) (bob (S.column r i)) ↔
      (r, i) ≠ (r₀, i₀)) :
    S.incidenceGame.success (deterministicCorrelation alice bob) =
      1 - (3 * (Fintype.card R : ℝ))⁻¹ := by
  classical
  rw [S.incidenceGame_deterministic_success]
  have he : (∑ p : R × Fin 3, if S.Accepts p.1 p.2 (alice p.1)
      (bob (S.column p.1 p.2)) then (1 : ℝ) else 0) =
      3 * (Fintype.card R : ℝ) - 1 := by
    simp_rw [h]
    have hterm (p : R × Fin 3) :
        (if p ≠ (r₀, i₀) then (1 : ℝ) else 0) =
          1 - if p = (r₀, i₀) then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [hterm]
    simp [Finset.sum_sub_distrib, Fintype.card_prod, mul_comm]
  rw [he, mul_sub, inv_mul_cancel₀, mul_one]
  positivity

end ThomGame.SparseSystem
