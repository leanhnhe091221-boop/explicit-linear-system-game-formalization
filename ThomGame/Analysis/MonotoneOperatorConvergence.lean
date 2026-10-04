module

public import ThomGame.Analysis.PositiveOperatorEstimates
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Monotone convergence of positive operators

A uniformly norm-bounded increasing family of positive operators on a
complex Hilbert space converges strongly. The index can be any nonempty
directed preorder. The resulting operator is the actual Loewner supremum.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {κ : Type*}

theorem monotone_operator_quadratic_bdd (f : κ → H →L[ℂ] H)
    (K : ℝ) (hbound : ∀ i, ‖f i‖ ≤ K) (x : H) :
    BddAbove (Set.range (fun i => (inner ℂ x (f i x)).re)) := by
  refine ⟨K * ‖x‖ ^ 2, ?_⟩
  rintro _ ⟨i, rfl⟩
  calc
    _ ≤ ‖inner ℂ x (f i x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖f i x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (K * ‖x‖) := mul_le_mul_of_nonneg_left
      ((f i).le_of_opNorm_le (hbound i) x) (norm_nonneg _)
    _ = _ := by ring

variable [CompleteSpace H] [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

theorem monotone_positive_operator_apply_cauchy (f : κ → H →L[ℂ] H)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i, ‖f i‖ ≤ K) (x : H) :
    Cauchy (Filter.map (fun i => f i x) atTop) := by
  let q : κ → ℝ := fun i => (inner ℂ x (f i x)).re
  have hqmono : Monotone q := fun i j hij => operator_re_inner_mono (hmono hij) x
  have hqbound : BddAbove (Set.range q) := monotone_operator_quadratic_bdd f K hbound x
  have hqt : Tendsto q atTop (𝓝 (⨆ i, q i)) := tendsto_atTop_ciSup hqmono hqbound
  have hdiff : Tendsto (fun i => (⨆ j, q j) - q i) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : κ => ⨆ j, q j) atTop (𝓝 (⨆ j, q j)) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub hqt
  apply Metric.cauchy_iff.2
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  let δ := (ε / 2) ^ 2 / (K + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := (hdiff.eventually (gt_mem_nhds hδ)).exists
  have hnear : ∀ i, N ≤ i → dist (f i x) (f N x) < ε / 2 := by
    intro i hi
    have hsubpos : 0 ≤ f i - f N := sub_nonneg.mpr (hmono hi)
    have hsubbound : ‖f i - f N‖ ≤ K :=
      (CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self _ (hpos N)) hsubpos).trans (hbound i)
    have he := positive_operator_apply_norm_sq_le (f i - f N) hsubpos K hK hsubbound x
    simp only [sub_apply, inner_sub_right, Complex.sub_re] at he
    change ‖f i x - f N x‖ ^ 2 ≤ K * (q i - q N) at he
    have hn : 0 ≤ q i - q N := sub_nonneg.mpr (hqmono hi)
    have hu : q i - q N ≤ (⨆ j, q j) - q N := sub_le_sub_right (le_ciSup hqbound i) _
    have hmul : K * (q i - q N) ≤ (K + 1) * ((⨆ j, q j) - q N) :=
      mul_le_mul (by linarith) hu hn (by positivity)
    have hsmall : (K + 1) * ((⨆ j, q j) - q N) < (ε / 2) ^ 2 := by
      calc
        _ < (K + 1) * δ := mul_lt_mul_of_pos_left hN (by positivity)
        _ = _ := by dsimp [δ]; field_simp
    rw [dist_eq_norm]
    nlinarith [he.trans hmul, norm_nonneg (f i x - f N x)]
  refine ⟨Metric.ball (f N x) (ε / 2), ?_, ?_⟩
  · exact eventually_atTop.2 ⟨N, fun i hi => hnear i hi⟩
  · intro a ha b hb
    have ht := dist_triangle a (f N x) b
    have ha' : dist a (f N x) < ε / 2 := ha
    have hb' : dist (f N x) b < ε / 2 := by simpa only [Metric.mem_ball, dist_comm] using hb
    linarith

theorem exists_monotone_positive_operator_limit (f : κ → H →L[ℂ] H)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i, ‖f i‖ ≤ K) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ ‖T‖ ≤ K ∧ IsLUB (Set.range f) T ∧
      (∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i)) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
  have hex : ∀ x : H, ∃ y : H, Tendsto (fun i => f i x) atTop (𝓝 y) :=
    fun x => cauchy_map_iff_exists_tendsto.mp (monotone_positive_operator_apply_cauchy f hmono hpos K hK hbound x)
  choose g hg using hex
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.2 ⟨K, by rintro _ ⟨i, rfl⟩; exact hbound i⟩
  let T := ContinuousLinearMap.ofTendstoOfBoundedRange g f (tendsto_pi_nhds.2 hg) hb
  have hs : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (T x)) := hg
  have hw : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i)) atTop
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.2
    intro x y
    exact tendsto_const_nhds.inner (hs x)
  refine ⟨T, (wot_nonneg_isClosed (H := H)).mem_of_tendsto hw (Eventually.of_forall hpos), ?_, ?_, hs, hw⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro x
    exact le_of_tendsto' (hs x).norm fun i => (f i).le_of_opNorm_le (hbound i) x
  · constructor
    · rintro _ ⟨i, rfl⟩
      exact (wot_le_isClosed (f i)).mem_of_tendsto hw
        ((eventually_ge_atTop i).mono fun _ hij => hmono hij)
    · intro B hB
      exact (wot_ge_isClosed B).mem_of_tendsto hw
        (Eventually.of_forall fun i => hB (Set.mem_range_self i))

end ThomGame.Analysis
