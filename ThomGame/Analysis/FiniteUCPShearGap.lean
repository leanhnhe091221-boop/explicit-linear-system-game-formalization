module

public import ThomGame.Analysis.FiniteUCPSOSTarget
public import ThomGame.Analysis.FiniteUCPWeakGapHeat

/-! The checked Netzer--Thom certificate gives a quantitative weak gap for
the actual six shears, including their restrictions from the double. -/

@[expose] public section
namespace ThomGame.Analysis
open ThomGame.Certificates.NetzerThom

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

variable {d : ℕ} [NeZero d]

theorem finiteSOS_shear_weakGap (f : MatrixAssignment Compressor.Root d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation IntegralShear.relators δ f) :
    FiniteMatrixWeakGap (finiteSOSShearTuple f) (1 / 144) (1000000000 * δ) := by
  intro X hX
  have hE := matrixCoordinateEnergy_nonneg (finiteSOSShearTuple f) X
  have hD : 0 ≤ 24 * matrixCoordinateEnergy (finiteSOSShearTuple f) X := by positivity
  have hc (r : Compressor.Root) : finiteNoDriftComm (f (FreeGroup.of r)) X ^ 2 ≤
      24 * matrixCoordinateEnergy (finiteSOSShearTuple f) X := by
    have hh := finiteNoDriftEnergy_single (finiteSOSShearTuple f) X
      ((Fintype.equivFinOfCardEq Compressor.root_card) r)
    simpa only [finiteSOSShearTuple, Equiv.symm_apply_apply, Nat.cast_ofNat,
      show (4 : ℝ) * 6 = 24 by norm_num] using hh
  have hl := matrix_certificate_lifting f hδ hf X hX
  rw [finiteSOS_target_quadratic] at hl
  have hr := matrix_certificate_residual f X hD hc
  have hg := matrix_certificate_gram_nonneg f X
  exact finiteSOS_NT_normalization hδ (finiteSOS_NT_numerical_repair hD hg hr hl)

omit [NeZero d] in
theorem finiteSOS_compressor_shear_model (f : Compressor.Generator → UnitaryMatrix d)
    {δ : ℝ} (hf : FiniteNoDriftCompressorModel f δ) :
    IsApproxRepresentation IntegralShear.relators δ (FreeGroup.lift (fun r => f (.inr r))) := by
  intro w hw
  obtain ⟨r, rfl⟩ := hw
  have hfamily (w : Word Compressor.Generator)
      (hw : w ∈ Compressor.shearComm ++ Compressor.shearRoot ++ Compressor.shearTorsion) :
      unitaryLength (Word.eval f w) ≤ δ := by
    apply hf
    simp only [List.mem_append] at hw
    simp only [Compressor.rawRelators, List.mem_append]
    tauto
  cases r with
  | separated p =>
    have hmem : Word.commutator (Compressor.shear p.val.1) (Compressor.shear p.val.2) ∈
        Compressor.shearComm := by
      apply List.mem_flatMap.mpr
      refine ⟨p.val.1, Compressor.mem_roots _, List.mem_flatMap.mpr
        ⟨p.val.2, Compressor.mem_roots _, ?_⟩⟩
      simp only [p.property, ↓reduceIte, List.mem_singleton]
    have hh := hfamily _ (by simp only [List.mem_append]; tauto)
    simpa only [IntegralShear.relator, Compressor.shear, PrimeFiveRankThreeCover.comm,
      map_mul, map_inv, FreeGroup.lift_apply_of, Word.eval_commutator, Word.eval_generator] using hh
  | adjacent r =>
    have hmem : Word.equation (Word.commutator (Compressor.shear r)
        (Compressor.shear (Compressor.right r))) (Compressor.shear (Compressor.across r)) ∈
        Compressor.shearRoot := List.mem_map.mpr ⟨r, Compressor.mem_roots r, rfl⟩
    have hh := hfamily _ (by simp only [List.mem_append]; tauto)
    simpa only [IntegralShear.relator, Compressor.shear, PrimeFiveRankThreeCover.comm,
      map_mul, map_inv, FreeGroup.lift_apply_of, Word.equation, Word.eval_append,
      Word.eval_inverse, Word.eval_commutator, Word.eval_generator] using hh
  | torsion =>
    have hmem : Compressor.power (Compressor.shear Compressor.root12 ++
        Word.inverse (Compressor.shear (Compressor.reverse Compressor.root12)) ++
        Compressor.shear Compressor.root12) 4 ∈ Compressor.shearTorsion := by
      simp [Compressor.shearTorsion]
    have hh := hfamily _ (by simp only [List.mem_append]; tauto)
    simpa [IntegralShear.relator, Compressor.power, Compressor.shear, pow_succ, mul_assoc] using hh

theorem finiteUCP_compressor_shear_weakGap (f : Compressor.Generator → UnitaryMatrix d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : FiniteNoDriftCompressorModel f δ) :
    FiniteMatrixWeakGap (finiteNoDriftShearTuple f) (1 / 144) (1000000000 * δ) := by
  have hh := finiteSOS_shear_weakGap (FreeGroup.lift (fun r => f (.inr r))) hδ
    (finiteSOS_compressor_shear_model f hf)
  have ht : finiteSOSShearTuple (FreeGroup.lift (fun r => f (.inr r))) =
      finiteNoDriftShearTuple f := by
    funext j
    exact FreeGroup.lift_apply_of
  rw [ht] at hh
  exact hh

theorem finiteUCP_double_shear_weakGap (f : MatrixAssignment Double.Generator d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : IsApproxRepresentation Double.relators δ f) (b : Bool) :
    FiniteMatrixWeakGap
      (finiteNoDriftShearTuple (fun g => f (FreeGroup.of (Double.copyGenerator b g))))
      (1 / 144) (1000000000 * δ) :=
  finiteUCP_compressor_shear_weakGap _ hδ (finiteNoDrift_copy_model f hf b)

end ThomGame.Analysis
