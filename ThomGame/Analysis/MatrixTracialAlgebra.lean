module

public import ThomGame.Analysis.MatrixNullIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual matrix quotient is a complex star algebra

Conjugate transpose descends through the proved two-sided 2-null ideal.
This equips the algebraic matrix quotient with its genuine star and
complex scalar operations; analytic completeness is a separate theorem.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (L : Filter ι)

theorem matrixQuotientMk_surjective : Function.Surjective (matrixQuotientMk dims L) :=
  Ideal.Quotient.mk_surjective

instance matrixTracialQuotientStar : Star (MatrixTracialQuotient dims L) where
  star := Quotient.lift (fun A => matrixQuotientMk dims L (star A)) (by
    intro A B h
    apply Ideal.Quotient.eq.mpr
    rw [← star_sub A B]
    exact matrixNullIdeal_star dims L (A - B) ((Submodule.quotientRel_def _).mp h))

@[simp] theorem matrixQuotientMk_star (A : BoundedMatrixSequence dims) :
    star (matrixQuotientMk dims L A) = matrixQuotientMk dims L (star A) := rfl

instance matrixTracialQuotientStarRing : StarRing (MatrixTracialQuotient dims L) where
  star_involutive x := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    simp only [matrixQuotientMk_star, star_star]
  star_mul x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    rw [← map_mul, matrixQuotientMk_star, star_mul, map_mul,
      matrixQuotientMk_star, matrixQuotientMk_star]
  star_add x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    rw [← map_add, matrixQuotientMk_star, star_add, map_add,
      matrixQuotientMk_star, matrixQuotientMk_star]

instance matrixTracialQuotientStarModule : StarModule ℂ (MatrixTracialQuotient dims L) where
  star_smul c x := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    change matrixQuotientMk dims L (star (c • A)) = matrixQuotientMk dims L (star c • star A)
    rw [star_smul]

def matrixQuotientStarAlgHom : BoundedMatrixSequence dims →⋆ₐ[ℂ] MatrixTracialQuotient dims L where
  __ := matrixQuotientMk dims L
  commutes' _c := rfl
  map_star' A := (matrixQuotientMk_star dims L A).symm

theorem matrixQuotient_one_ne_zero [L.NeBot] (hd : ∀ i, 0 < dims i) :
    (1 : MatrixTracialQuotient dims L) ≠ 0 := by
  intro he
  have h := (matrixQuotientMk_eq_zero_iff dims L 1).mp (by simpa only [map_one] using he)
  have hone (i : ι) : hsNorm ((1 : BoundedMatrixSequence dims).val i) = 1 := by
    let : NeZero (dims i) := ⟨Nat.ne_of_gt (hd i)⟩
    exact hsNorm_one
  simp_rw [hone] at h
  exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds)

end ThomGame.Analysis
