module

public import ThomGame.Analysis.MatrixMaximalProjectionFamilies
public import ThomGame.Analysis.MatrixProjectionDistance
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# A large projection excluding two bad families

Choose the second maximal family in the orthogonal complement of the
first. Their combined orthogonal sum has trace bounded by the sum of
the two family bounds, and its complement excludes both predicates.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {d : Nat} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem normalizedTrace_sum (s : Finset ι) (X : ι → CMatrix d) :
    normalizedTrace (∑ i ∈ s, X i) = ∑ i ∈ s, normalizedTrace (X i) := by
  simp only [normalizedTrace, Matrix.trace_sum, Finset.sum_div]

theorem matrixOrthogonalSum_complement_orthogonal (P : ι → CMatrix d)
    (hP : ∀ i, IsStarProjection (P i)) (horth : Pairwise (fun i j => P i * P j = 0))
    {Q : CMatrix d} (hQ : IsStarProjection Q) (hle : Q ≤ 1 - ∑ i, P i) :
    ∀ i, P i * Q = 0 := by
  have hsum := matrixOrthogonalSum_projection P hP horth
  have hr := (hQ.le_iff_mul_eq_right hsum.one_sub).1 hle
  rw [sub_mul, one_mul, sub_eq_self] at hr
  have hi := OrthogonalIdempotents.mk (fun i => (hP i).isIdempotentElem) horth
  intro i
  rw [← hi.mul_sum_of_mem (Finset.mem_univ i), mul_assoc, hr, mul_zero]

variable [NeZero d]

theorem exists_matrixProjection_excluding_two (B C : CMatrix d → Prop)
    (hB : ∀ P, B P → IsStarProjection P ∧ P ≠ 0)
    (hC : ∀ P, C P → IsStarProjection P ∧ P ≠ 0) (b c : ℝ)
    (hBt : ∀ s : Finset (CMatrix d), (∀ P ∈ s, B P) →
      (s : Set (CMatrix d)).Pairwise (fun P Q => P * Q = 0) →
        (∑ P ∈ s, (normalizedTrace P).re) ≤ b)
    (hCt : ∀ s : Finset (CMatrix d), (∀ P ∈ s, C P) →
      (s : Set (CMatrix d)).Pairwise (fun P Q => P * Q = 0) →
        (∑ P ∈ s, (normalizedTrace P).re) ≤ c) :
    ∃ R : CMatrix d, IsStarProjection R ∧ (normalizedTrace (1 - R)).re ≤ b + c ∧
      (normalizedTrace (1 - R)).re ≤ 1 ∧
      ∀ P, IsStarProjection P → P ≤ R → ¬B P ∧ ¬C P := by
  classical
  obtain ⟨s, hsB, hsorth, hsmax⟩ := exists_matrixMaximalOrthogonalFamily B hB
  let D : CMatrix d → Prop := fun Q => C Q ∧ ∀ P ∈ s, P * Q = 0
  obtain ⟨t, htD, htorth, htmax⟩ := exists_matrixMaximalOrthogonalFamily D (fun Q hQ => hC Q hQ.1)
  let W : Sum s t → CMatrix d := Sum.elim Subtype.val Subtype.val
  have hW (i : Sum s t) : IsStarProjection (W i) := by
    cases i with
    | inl i => exact (hB i.val (hsB i.val i.prop)).1
    | inr i => exact (hC i.val (htD i.val i.prop).1).1
  have hWorth : Pairwise (fun i j => W i * W j = 0) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hsorth i.prop j.prop (fun he => hij (congrArg Sum.inl (Subtype.ext he)))
      | inr j => exact (htD j.val j.prop).2 i.val i.prop
    | inr i =>
      cases j with
      | inl j =>
        exact matrixProjection_mul_zero_symm (hW (.inl j)) (hW (.inr i))
          ((htD i.val i.prop).2 j.val j.prop)
      | inr j => exact htorth i.prop j.prop (fun he => hij (congrArg Sum.inr (Subtype.ext he)))
  let R : CMatrix d := 1 - ∑ i, W i
  have hR : IsStarProjection R := (matrixOrthogonalSum_projection W hW hWorth).one_sub
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · have he : (normalizedTrace (1 - R)).re =
        (∑ P ∈ s, (normalizedTrace P).re) + ∑ P ∈ t, (normalizedTrace P).re := by
      simp only [R, sub_sub_cancel]
      rw [normalizedTrace_sum, Complex.re_sum]
      simp only [Fintype.sum_sum_type, W, Sum.elim_inl, Sum.elim_inr]
      exact congrArg₂ (· + ·) (Finset.sum_coe_sort s (fun P : CMatrix d => (normalizedTrace P).re))
        (Finset.sum_coe_sort t (fun P : CMatrix d => (normalizedTrace P).re))
    rw [he]
    exact add_le_add (hBt s hsB hsorth) (hCt t (fun P hP => (htD P hP).1) htorth)
  · have htR := (Complex.nonneg_iff.mp (normalizedTrace_nonneg R hR.nonneg)).1
    rw [normalizedTrace_sub, normalizedTrace_one, Complex.sub_re, Complex.one_re]
    linarith
  · intro Q hQ hQR
    have he := matrixOrthogonalSum_complement_orthogonal W hW hWorth hQ hQR
    constructor
    · intro hBQ
      exact hsmax Q hBQ (fun P hP => he (.inl ⟨P, hP⟩))
    · intro hCQ
      exact htmax Q ⟨hCQ, fun P hP => he (.inl ⟨P, hP⟩)⟩ (fun P hP => he (.inr ⟨P, hP⟩))

end ThomGame.Analysis
