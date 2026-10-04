module

public import ThomGame.Analysis.MatrixFiniteExpectation
public import ThomGame.Analysis.MatrixInternalNormalTrace

/-!
# Normality of the internal conditional expectation

Positivity and monotone completeness give a supremum of the expected
positive family. Normality and preservation of the faithful trace force
this supremum to equal the expectation of the original supremum.
The directed index set is arbitrary.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

theorem matrixFiniteExpectation_realTrace (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRealTrace dims hd U (matrixFiniteExpectation dims S hd U hU T) =
      matrixFiniteRealTrace dims hd U T :=
  congrArg Complex.re (matrixFiniteExpectation_trace dims S hd U hU T)

theorem matrixFiniteExpectation_faithful (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteExpectation dims S hd U hU (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply (matrixFiniteTrace_faithful dims hd U T).mp
    rw [← matrixFiniteExpectation_trace dims S hd U hU, h, map_zero]
  · rintro rfl
    simp only [star_zero, mul_zero, map_zero]

theorem matrixFiniteExpectation_nonneg_eq_zero_iff (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : 0 ≤ T) : matrixFiniteExpectation dims S hd U hU T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply eq_zero_of_nonneg_of_faithful_trace (matrixFiniteRealTrace dims hd U)
      (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp) T hT
    rw [← matrixFiniteExpectation_realTrace dims S hd U hU, h, map_zero]
  · rintro rfl
    exact map_zero _

noncomputable def matrixInternalExpectation :
    MatrixFiniteOperatorAlgebra dims hd U →ₗ[ℂ] matrixInternalFiniteAlgebra dims S hd U :=
  (matrixFiniteExpectation dims S hd U hU).codRestrict
    (matrixInternalFiniteAlgebra dims S hd U).toSubalgebra.toSubmodule
    (matrixFiniteExpectation_mem dims S hd U hU)

@[simp] theorem matrixInternalExpectation_val (T : MatrixFiniteOperatorAlgebra dims hd U) :
    (matrixInternalExpectation dims S hd U hU T).val = matrixFiniteExpectation dims S hd U hU T := rfl

theorem matrixInternalExpectation_eq_self (T : matrixInternalFiniteAlgebra dims S hd U) :
    matrixInternalExpectation dims S hd U hU T.val = T :=
  Subtype.ext (matrixFiniteExpectation_eq_self dims S hd U hU T.val T.property)

theorem matrixInternalExpectation_trace (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixInternalFiniteTrace dims S hd U (matrixInternalExpectation dims S hd U hU T) =
      matrixFiniteTrace dims hd U T :=
  matrixFiniteExpectation_trace dims S hd U hU T

variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

theorem matrixFiniteExpectation_preserves_positive_sup
    (f : κ → MatrixFiniteOperatorAlgebra dims hd U) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixFiniteExpectation dims S hd U hU (f i)))
      (matrixFiniteExpectation dims S hd U hU T) := by
  have hemono := (matrixFiniteExpectation_monotone dims S hd U hU).comp hmono
  have hepos := fun i => matrixFiniteExpectation_nonneg dims S hd U hU (f i) (hpos i)
  have heupper : matrixFiniteExpectation dims S hd U hU T ∈
      upperBounds (Set.range (fun i => matrixFiniteExpectation dims S hd U hU (f i))) := by
    rintro _ ⟨i, rfl⟩
    exact matrixFiniteExpectation_monotone dims S hd U hU (hT.1 (Set.mem_range_self i))
  obtain ⟨R, _, hR, _, _⟩ := exists_matrixFinite_positive_sup dims hd U
    (fun i => matrixFiniteExpectation dims S hd U hU (f i)) hemono hepos ⟨_, heupper⟩
  have hτR := matrixFiniteRealTrace_preserves_positive_sup dims hd U
    (fun i => matrixFiniteExpectation dims S hd U hU (f i)) hemono hepos R hR
  simp only [matrixFiniteExpectation_realTrace] at hτR
  have hτT := matrixFiniteRealTrace_preserves_positive_sup dims hd U f hmono hpos T hT
  have hEq : R = matrixFiniteExpectation dims S hd U hU T :=
    eq_of_le_of_faithful_trace (matrixFiniteRealTrace dims hd U)
      (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp) R _ (hR.2 heupper)
      ((hτR.unique hτT).trans (matrixFiniteExpectation_realTrace dims S hd U hU T).symm)
  exact hEq ▸ hR

theorem matrixFiniteExpectation_positive_tendsto_sup
    (f : κ → MatrixFiniteOperatorAlgebra dims hd U) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    (∀ ξ, Tendsto (fun i => (matrixFiniteExpectation dims S hd U hU (f i)).val ξ) atTop
      (𝓝 ((matrixFiniteExpectation dims S hd U hU T).val ξ))) ∧
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (matrixFiniteExpectation dims S hd U hU (f i)).val)
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (matrixFiniteExpectation dims S hd U hU T).val)) :=
  matrixFinite_positive_tendsto_sup dims hd U (fun i => matrixFiniteExpectation dims S hd U hU (f i))
    ((matrixFiniteExpectation_monotone dims S hd U hU).comp hmono)
    (fun i => matrixFiniteExpectation_nonneg dims S hd U hU (f i) (hpos i)) _
    (matrixFiniteExpectation_preserves_positive_sup dims S hd U hU f hmono hpos T hT)

theorem matrixInternalExpectation_preserves_positive_sup
    (f : κ → MatrixFiniteOperatorAlgebra dims hd U) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixInternalExpectation dims S hd U hU (f i)))
      (matrixInternalExpectation dims S hd U hU T) := by
  have he := matrixFiniteExpectation_preserves_positive_sup dims S hd U hU f hmono hpos T hT
  constructor
  · rintro _ ⟨i, rfl⟩
    change matrixFiniteExpectation dims S hd U hU (f i) ≤ matrixFiniteExpectation dims S hd U hU T
    exact he.1 (Set.mem_range_self i)
  · intro B hB
    change matrixFiniteExpectation dims S hd U hU T ≤ B.val
    apply he.2
    rintro _ ⟨i, rfl⟩
    have hi := hB (Set.mem_range_self i)
    change matrixFiniteExpectation dims S hd U hU (f i) ≤ B.val at hi
    exact hi

theorem matrixFiniteExpectation_normal (s : Set (MatrixFiniteOperatorAlgebra dims hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB s T) :
    IsLUB (matrixFiniteExpectation dims S hd U hU '' s) (matrixFiniteExpectation dims S hd U hU T) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  have h := matrixFiniteExpectation_preserves_positive_sup dims S hd U hU (fun a : s => a.val)
    (fun _ _ hab => hab) (fun a => hpos a.val a.property) T (hr.symm ▸ hT)
  have he : Set.range (fun a : s => matrixFiniteExpectation dims S hd U hU a.val) =
      matrixFiniteExpectation dims S hd U hU '' s := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact he ▸ h

end ThomGame.Analysis
