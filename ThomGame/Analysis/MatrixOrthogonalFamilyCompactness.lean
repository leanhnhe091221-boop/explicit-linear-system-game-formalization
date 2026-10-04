module

public import ThomGame.Analysis.MatrixALTLogarithmicFamily

/-!
# Compactness of actual orthogonal partial-isometry families

All constraints are closed matrix equations. A partial isometry lies
in the operator-norm unit ball, so their finite product is compact.
The continuous objective measures energy and excess missing trace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {μ : Type*} {d h : Nat}

def matrixOrthogonalFamilySpace (q : μ → CMatrix d) : Set (μ → CMatrix d) :=
  {V | (∀ i, IsStarProjection ((V i)ᴴ * V i)) ∧
    (∀ i, (V i * (V i)ᴴ) * q i = V i * (V i)ᴴ) ∧
    Pairwise (fun i j => ((V i)ᴴ * V i) * ((V j)ᴴ * V j) = 0)}

theorem isClosed_matrixStarProjection : IsClosed {P : CMatrix d | IsStarProjection P} := by
  have hm : Continuous (fun P : CMatrix d => P * P) := continuous_id.mul continuous_id
  simpa only [isStarProjection_iff', Set.ofPred_and, id_eq] using
    (isClosed_eq hm continuous_id).inter (isClosed_eq continuous_star continuous_id)

theorem matrixOrthogonalFamilySpace_isClosed (q : μ → CMatrix d) :
    IsClosed (matrixOrthogonalFamilySpace q) := by
  have hi (i : μ) : Continuous (fun V : μ → CMatrix d => (V i)ᴴ * V i) :=
    (continuous_apply i).star.mul (continuous_apply i)
  have hf (i : μ) : Continuous (fun V : μ → CMatrix d => V i * (V i)ᴴ) :=
    (continuous_apply i).mul (continuous_apply i).star
  simp only [matrixOrthogonalFamilySpace, Set.ofPred_and, Set.ofPred_forall, Pairwise]
  refine (isClosed_iInter fun i => isClosed_matrixStarProjection.preimage (hi i)).inter
    ((isClosed_iInter fun i => isClosed_eq ((hf i).mul continuous_const) (hf i)).inter ?_)
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq ((hi i).mul (hi j)) continuous_const

theorem matrixOrthogonalFamilySpace_nonempty (q : μ → CMatrix d) :
    (matrixOrthogonalFamilySpace q).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp [matrixOrthogonalFamilySpace, Pairwise]

theorem matrixOrthogonalFamilySpace_isCompact (q : μ → CMatrix d) :
    IsCompact (matrixOrthogonalFamilySpace q) := by
  apply (isCompact_pi_infinite (fun _ : μ => isCompact_closedBall (0 : CMatrix d) 1)).of_isClosed_subset
    (matrixOrthogonalFamilySpace_isClosed q)
  intro V hV i
  simpa only [Metric.mem_closedBall, dist_zero_right, matrixOpNorm] using
    matrixPartialIsometry_norm_le_one (hV.1 i)

theorem matrixOrthogonalFamilySpace_final_le {q : μ → CMatrix d}
    (hq : ∀ i, IsStarProjection (q i)) {V : μ → CMatrix d}
    (hV : V ∈ matrixOrthogonalFamilySpace q) (i : μ) :
    V i * (V i)ᴴ ≤ q i :=
  ((matrixPartialIsometry_final_projection (hV.1 i)).le_iff_mul_eq_left (hq i)).mpr (hV.2.1 i)

variable [Fintype μ]

noncomputable def matrixOrthogonalFamilyDefect (U : Fin h → UnitaryMatrix d)
    (q V : μ → CMatrix d) : ℝ :=
  (∑ i, matrixCoordinateEnergy U (V i)) +
    max (matrixTraceReal d (1 - ∑ i, (V i)ᴴ * V i) - matrixFamilyCoverageDefect q) 0

theorem matrixOrthogonalFamilyDefect_nonneg (U : Fin h → UnitaryMatrix d)
    (q V : μ → CMatrix d) : 0 ≤ matrixOrthogonalFamilyDefect U q V :=
  add_nonneg (Finset.sum_nonneg fun i _ => matrixCoordinateEnergy_nonneg U (V i)) (le_max_right _ _)

variable [NeZero d]

theorem matrixOrthogonalFamilyDefect_continuous (U : Fin h → UnitaryMatrix d)
    (q : μ → CMatrix d) : Continuous (matrixOrthogonalFamilyDefect U q) := by
  have he : Continuous (fun V : μ → CMatrix d => ∑ i, matrixCoordinateEnergy U (V i)) :=
    continuous_finsetSum _ fun i _ => (matrixCoordinateEnergy_continuous U).comp (continuous_apply i)
  have hi : Continuous (fun V : μ → CMatrix d => ∑ i, (V i)ᴴ * V i) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).star.mul (continuous_apply i)
  have htr : Continuous (matrixTraceReal d : CMatrix d → ℝ) := (matrixTraceRealCLM d).continuous
  exact he.add (((htr.comp (continuous_const.sub hi)).sub continuous_const).max continuous_const)

theorem exists_matrixOrthogonalFamilyDefect_minimizer (U : Fin h → UnitaryMatrix d)
    (q : μ → CMatrix d) :
    ∃ V ∈ matrixOrthogonalFamilySpace q, ∀ W ∈ matrixOrthogonalFamilySpace q,
      matrixOrthogonalFamilyDefect U q V ≤ matrixOrthogonalFamilyDefect U q W := by
  obtain ⟨V, hV, hmin⟩ := (matrixOrthogonalFamilySpace_isCompact q).exists_isMinOn
    (matrixOrthogonalFamilySpace_nonempty q) (matrixOrthogonalFamilyDefect_continuous U q).continuousOn
  exact ⟨V, hV, fun W hW => hmin hW⟩

end ThomGame.Analysis
