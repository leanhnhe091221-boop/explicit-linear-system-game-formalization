module

public import ThomGame.Analysis.MatrixStandardBlockCutProjections
public import ThomGame.Analysis.MatrixSubalgebraConcreteBlocks

/-!
# Actual block cuts inside a matrix algebra and its commutant

The star block coordinates construct one projection in A and one in A'.
Their product realizes simultaneous cuts in the two factors, with rank
equal to the exact sum of retained block dimensions.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

theorem matrixInitialProjection_family {n : Nat} (p r : Fin n → Nat) :
    IsStarProjection (fun i => matrixInitialProjection (p i) (r i)) := by
  constructor
  · funext i
    exact (matrixInitialProjection_isStarProjection (p i) (r i)).isIdempotentElem.eq
  · funext i
    exact (matrixInitialProjection_isStarProjection (p i) (r i)).isSelfAdjoint.star_eq

variable {m : Nat} (A : StarSubalgebra ℂ (CMatrix m)) (R : MatrixSubalgebraStarBlocks A)

theorem matrixStarRepresentationCoordinates_rank {d : Nat} (ρ : A →⋆ₐ[ℂ] CMatrix d) (X : CMatrix d) :
    (matrixStarRepresentationCoordinates A R ρ X).rank = X.rank := by
  rw [matrixStarRepresentationCoordinates_apply, Matrix.rank_reindex]
  change ((star (matrixStarRepresentationUnitary A R ρ) : CMatrix d) * X *
    (matrixStarRepresentationUnitary A R ρ : CMatrix d)).rank = X.rank
  rw [← Unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -Unitary.coe_star]

noncomputable def matrixSubalgebraFactorCut (r : Fin R.count → Nat) : CMatrix m :=
  matrixStarRepresentationBlocks A R A.subtype (fun i => matrixInitialProjection (R.size i) (r i))

noncomputable def matrixSubalgebraMultiplicityCut (s : Fin R.count → Nat) : CMatrix m :=
  matrixStarRepresentationComplementary A R A.subtype
    (fun i => matrixInitialProjection (matrixStarRepresentationMultiplicity A R A.subtype i) (s i))

theorem matrixSubalgebraFactorCut_projection (r : Fin R.count → Nat) :
    IsStarProjection (matrixSubalgebraFactorCut A R r) :=
  (matrixInitialProjection_family R.size r).map (matrixStarRepresentationBlocks A R A.subtype)

theorem matrixSubalgebraMultiplicityCut_projection (s : Fin R.count → Nat) :
    IsStarProjection (matrixSubalgebraMultiplicityCut A R s) :=
  (matrixInitialProjection_family (matrixStarRepresentationMultiplicity A R A.subtype) s).map
    (matrixStarRepresentationComplementary A R A.subtype)

theorem matrixSubalgebraFactorCut_mem (r : Fin R.count → Nat) : matrixSubalgebraFactorCut A R r ∈ A := by
  have h : matrixSubalgebraFactorCut A R r ∈ (matrixStarRepresentationBlocks A R A.subtype).range :=
    ⟨fun i => matrixInitialProjection (R.size i) (r i), rfl⟩
  exact (le_of_eq (matrixSubalgebra_eq_standard_blocks A R).symm) h

theorem matrixSubalgebraMultiplicityCut_mem (s : Fin R.count → Nat) :
    matrixSubalgebraMultiplicityCut A R s ∈ StarSubalgebra.centralizer ℂ (A : Set (CMatrix m)) := by
  have he := matrixStarRepresentation_commutant_eq A R A.subtype
  rw [matrixSubalgebra_subtype_range] at he
  rw [he]
  exact ⟨fun i => matrixInitialProjection (matrixStarRepresentationMultiplicity A R A.subtype i) (s i), rfl⟩

theorem matrixSubalgebraCuts_commute (r s : Fin R.count → Nat) :
    Commute (matrixSubalgebraFactorCut A R r) (matrixSubalgebraMultiplicityCut A R s) :=
  (mem_matrixSubalgebraCommutant_iff A _).mp (matrixSubalgebraMultiplicityCut_mem A R s)
    _ (matrixSubalgebraFactorCut_mem A R r)

theorem matrixSubalgebraCuts_product_projection (r s : Fin R.count → Nat) :
    IsStarProjection (matrixSubalgebraFactorCut A R r * matrixSubalgebraMultiplicityCut A R s) :=
  (matrixSubalgebraFactorCut_projection A R r).mul (matrixSubalgebraMultiplicityCut_projection A R s)
    (matrixSubalgebraCuts_commute A R r s)

theorem matrixSubalgebraCuts_product_rank (r s : Fin R.count → Nat)
    (hr : ∀ i, r i ≤ R.size i) (hs : ∀ i, s i ≤ matrixStarRepresentationMultiplicity A R A.subtype i) :
    (matrixSubalgebraFactorCut A R r * matrixSubalgebraMultiplicityCut A R s).rank = ∑ i, r i * s i := by
  rw [← matrixStarRepresentationCoordinates_rank A R A.subtype, map_mul]
  unfold matrixSubalgebraFactorCut matrixSubalgebraMultiplicityCut
  rw [matrixStarRepresentationCoordinates_blocks, matrixStarRepresentationCoordinates_complementary]
  exact matrixStandardBlockCuts_product_rank R.size (matrixStarRepresentationMultiplicity A R A.subtype) r s hr hs

end ThomGame.Analysis
