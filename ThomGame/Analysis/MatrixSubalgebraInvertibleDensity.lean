module

public import ThomGame.Analysis.MatrixSubalgebraPolar
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Invertible matrices are dense inside every unital matrix subalgebra

The complex spectrum is finite. Arbitrarily small scalar shifts avoid
it, stay in the given subalgebra, and give actual invertible matrices.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped Matrix.Norms.L2Operator

variable {d : Nat}

theorem matrixSubalgebra_mem_closure_isUnit (A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ A) : X ∈ closure {Y : CMatrix d | Y ∈ A ∧ IsUnit Y} := by
  let f : ℂ → CMatrix d := fun z => X - z • 1
  have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
  have hz : (0 : ℂ) ∈ closure (spectrum ℂ X)ᶜ := (X.finite_spectrum.countable.dense_compl ℂ) 0
  have him : f 0 ∈ closure (f '' (spectrum ℂ X)ᶜ) :=
    image_closure_subset_closure_image hf ⟨0, hz, rfl⟩
  have hsub : f '' (spectrum ℂ X)ᶜ ⊆ {Y : CMatrix d | Y ∈ A ∧ IsUnit Y} := by
    rintro Y ⟨z, hz, rfl⟩
    refine ⟨A.sub_mem hX (A.smul_mem A.one_mem z), ?_⟩
    have hi : IsUnit (algebraMap ℂ (CMatrix d) z - X) := by
      simpa only [Set.mem_compl_iff, spectrum.mem_iff, not_not] using hz
    simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hi.neg
  simpa only [f, zero_smul, sub_zero] using (closure_mono hsub) him

theorem exists_matrixSubalgebra_invertible_near (A : StarSubalgebra ℂ (CMatrix d))
    {X : CMatrix d} (hX : X ∈ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : CMatrix d, Y ∈ A ∧ IsUnit Y ∧ matrixOpNorm (X - Y) < ε := by
  obtain ⟨Y, hY, hd⟩ := Metric.mem_closure_iff.mp (matrixSubalgebra_mem_closure_isUnit A hX) ε hε
  exact ⟨Y, hY.1, hY.2, by simpa only [dist_eq_norm, norm_sub_rev, matrixOpNorm] using hd⟩

end ThomGame.Analysis
