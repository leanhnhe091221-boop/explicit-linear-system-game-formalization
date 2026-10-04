module

public import ThomGame.Analysis.MatrixNormControlledRepresentatives
public import ThomGame.Analysis.MatrixBoundedWOTBall

/-!
# The original represented matrix quotient is norm closed

A norm-convergent sequence of represented operators is eventually
uniformly bounded. The norm-controlled representative theorem puts its
tail inside one fixed representative ball, which is WOT closed. The
limit is therefore represented as well. This proves norm closedness of
the original image, without identifying it with its WOT closure.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

noncomputable def matrixRepresentedAlgebra :
    StarSubalgebra ℂ (MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U) :=
  (matrixLeftRepresentation dims hd U).range

noncomputable def matrixRepresentedEquiv :
    MatrixTracialQuotient dims (U : Filter Nat) ≃⋆ₐ[ℂ] matrixRepresentedAlgebra dims hd U :=
  StarAlgEquiv.ofInjective (matrixLeftRepresentation dims hd U) (matrixLeftRepresentation_injective dims hd U)

@[simp] theorem matrixRepresentedEquiv_apply (x : MatrixTracialQuotient dims (U : Filter Nat)) :
    (matrixRepresentedEquiv dims hd U x).val = matrixLeftRepresentation dims hd U x := rfl

theorem matrixRepresentedAlgebra_isClosed (hU : (U : Filter Nat) ≤ atTop) :
    IsClosed (matrixRepresentedAlgebra dims hd U :
      Set (MatrixTraceHilbert dims hd U →L[ℂ] MatrixTraceHilbert dims hd U)) := by
  apply IsSeqClosed.isClosed
  intro v T hv hvT
  let K := ‖T‖ + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hev : ∀ᶠ n in atTop, ‖v n‖ ≤ K :=
    (hvT.norm.eventually (gt_mem_nhds (by dsimp [K]; linarith))).mono (fun _ h => h.le)
  have hb : ∀ᶠ n in atTop, ContinuousLinearMapWOT.ofCLM (v n) ∈ matrixBoundedWOTBall dims hd U (2 * K) := by
    filter_upwards [hev] with n hn
    obtain ⟨x, hx⟩ := hv n
    obtain ⟨A, hA, hAx⟩ := exists_matrixRepresentative_bounded dims hd U x K hK (hx ▸ hn)
    refine ⟨A, hA, ?_⟩
    rw [hAx]
    exact congrArg ContinuousLinearMapWOT.ofCLM hx
  have ht : ContinuousLinearMapWOT.ofCLM T ∈ matrixBoundedWOTBall dims hd U (2 * K) :=
    (matrixBoundedWOTBall_isClosed dims hd U hU (2 * K) (by positivity)).mem_of_tendsto
      (ContinuousLinearMapWOT.continuous_ofCLM.continuousAt.tendsto.comp hvT) hb
  obtain ⟨A, _, hA⟩ := ht
  exact ⟨matrixQuotientMk dims (U : Filter Nat) A, congrArg ContinuousLinearMapWOT.toCLM hA⟩

instance matrixRepresentedAlgebra_hyperfilter_isClosed :
    IsClosed (matrixRepresentedAlgebra dims hd (hyperfilter Nat) :
      Set (MatrixTraceHilbert dims hd (hyperfilter Nat) →L[ℂ]
        MatrixTraceHilbert dims hd (hyperfilter Nat))) :=
  matrixRepresentedAlgebra_isClosed dims hd (hyperfilter Nat) Nat.hyperfilter_le_atTop

noncomputable abbrev MatrixRepresentedCStarAlgebra := matrixRepresentedAlgebra dims hd (hyperfilter Nat)

end ThomGame.Analysis
