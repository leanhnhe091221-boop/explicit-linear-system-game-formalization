module

public import ThomGame.Analysis.MatrixAnchoredScaleCoordinates
public import ThomGame.Analysis.MatrixQuotientAnchor

/-!
# The actual bounded conditional-median sequence

The coordinate construction is uniformly contractive and lies in the
specified internal algebra. Its coordinate expectation is exactly half
the identity on every original matrix space.
-/

@[expose] public section
namespace ThomGame.Analysis

variable {ι : Type*} (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (F : (n : ι) → MatrixSubalgebraStarBlocks (D n))
    (R : (n : ι) → MatrixSubalgebraStarBlocks
      (StarSubalgebra.centralizer ℂ (A n : Set (CMatrix (dims n)))))
    (hDA : ∀ n, D n ≤ A n)

noncomputable def matrixAnchoredScaleSequence : BoundedMatrixSequence dims :=
  ⟨fun n => matrixAnchoredBoundedScale (D n) (A n) (F n) (R n) (hDA n),
    1, zero_le_one, fun n => (matrixAnchoredBoundedScale_spec (D n) (A n) (F n) (R n) (hDA n)).2.2.2⟩

theorem matrixAnchoredScaleSequence_mem (n : ι) :
    (matrixAnchoredScaleSequence dims A D F R hDA).val n ∈ A n :=
  (matrixAnchoredBoundedScale_spec (D n) (A n) (F n) (R n) (hDA n)).2.2.1

theorem matrixAnchoredScaleSequence_expectation (n : ι) :
    matrixTraceProjection (D n) ((matrixAnchoredScaleSequence dims A D F R hDA).val n) = (1 / 2 : ℂ) • 1 :=
  matrixAnchoredBoundedScale_expectation (D n) (A n) (F n) (R n) (hDA n)

theorem matrixAnchoredScaleSequence_mem_internal (L : Filter ι) :
    matrixQuotientMk dims L (matrixAnchoredScaleSequence dims A D F R hDA) ∈ matrixInternalQuotient dims A L :=
  (mem_matrixInternalQuotient dims A L _).mpr
    ⟨matrixAnchoredScaleSequence dims A D F R hDA, matrixAnchoredScaleSequence_mem dims A D F R hDA, rfl⟩

end ThomGame.Analysis
