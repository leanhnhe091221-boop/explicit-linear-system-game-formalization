module

public import ThomGame.Analysis.MatrixFiniteRelativeExpectation
public import ThomGame.Analysis.MatrixNormalTrace

/-!
# Faithfulness and normality of the relative-commutant expectation

The actual positive trace-preserving expectation preserves every
existing supremum of a nonempty positive directed family. Normality
of the faithful ambient trace forces equality with the supremum of
the expected family. No internality of the commutant is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (V : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat) (hU : (U : Filter Nat) ≤ atTop)

theorem matrixFiniteRelativeExpectation_realTrace (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRealTrace dims hd U (matrixFiniteRelativeExpectation dims V hd U hU T) =
      matrixFiniteRealTrace dims hd U T :=
  congrArg Complex.re (matrixFiniteRelativeExpectation_trace dims V hd U hU T)

theorem matrixFiniteRelativeExpectation_faithful (T : MatrixFiniteOperatorAlgebra dims hd U) :
    matrixFiniteRelativeExpectation dims V hd U hU (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply (matrixFiniteTrace_faithful dims hd U T).mp
    rw [← matrixFiniteRelativeExpectation_trace dims V hd U hU, h, map_zero]
  · rintro rfl
    simp only [star_zero, mul_zero, map_zero]

theorem matrixFiniteRelativeExpectation_nonneg_eq_zero_iff (T : MatrixFiniteOperatorAlgebra dims hd U)
    (hT : 0 ≤ T) : matrixFiniteRelativeExpectation dims V hd U hU T = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply eq_zero_of_nonneg_of_faithful_trace (matrixFiniteRealTrace dims hd U)
      (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp) T hT
    rw [← matrixFiniteRelativeExpectation_realTrace dims V hd U hU, h, map_zero]
  · rintro rfl
    exact map_zero _

variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

theorem matrixFiniteRelativeExpectation_preserves_positive_sup
    (f : κ → MatrixFiniteOperatorAlgebra dims hd U) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixFiniteRelativeExpectation dims V hd U hU (f i)))
      (matrixFiniteRelativeExpectation dims V hd U hU T) := by
  have hemono := (matrixFiniteRelativeExpectation_monotone dims V hd U hU).comp hmono
  have hepos := fun i => matrixFiniteRelativeExpectation_nonneg dims V hd U hU (f i) (hpos i)
  have heupper : matrixFiniteRelativeExpectation dims V hd U hU T ∈
      upperBounds (Set.range (fun i => matrixFiniteRelativeExpectation dims V hd U hU (f i))) := by
    rintro _ ⟨i, rfl⟩
    exact matrixFiniteRelativeExpectation_monotone dims V hd U hU (hT.1 (Set.mem_range_self i))
  obtain ⟨R, _, hR, _, _⟩ := exists_matrixFinite_positive_sup dims hd U
    (fun i => matrixFiniteRelativeExpectation dims V hd U hU (f i)) hemono hepos ⟨_, heupper⟩
  have hτR := matrixFiniteRealTrace_preserves_positive_sup dims hd U
    (fun i => matrixFiniteRelativeExpectation dims V hd U hU (f i)) hemono hepos R hR
  simp only [matrixFiniteRelativeExpectation_realTrace] at hτR
  have hτT := matrixFiniteRealTrace_preserves_positive_sup dims hd U f hmono hpos T hT
  have hEq : R = matrixFiniteRelativeExpectation dims V hd U hU T :=
    eq_of_le_of_faithful_trace (matrixFiniteRealTrace dims hd U)
      (fun a => (matrixFiniteRealTrace_faithful dims hd U a).mp) R _ (hR.2 heupper)
      ((hτR.unique hτT).trans (matrixFiniteRelativeExpectation_realTrace dims V hd U hU T).symm)
  exact hEq ▸ hR

theorem matrixFiniteRelativeExpectation_positive_tendsto_sup
    (f : κ → MatrixFiniteOperatorAlgebra dims hd U) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    (∀ ξ, Tendsto (fun i => (matrixFiniteRelativeExpectation dims V hd U hU (f i)).val ξ) atTop
      (𝓝 ((matrixFiniteRelativeExpectation dims V hd U hU T).val ξ))) ∧
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (matrixFiniteRelativeExpectation dims V hd U hU (f i)).val)
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (matrixFiniteRelativeExpectation dims V hd U hU T).val)) :=
  matrixFinite_positive_tendsto_sup dims hd U (fun i => matrixFiniteRelativeExpectation dims V hd U hU (f i))
    ((matrixFiniteRelativeExpectation_monotone dims V hd U hU).comp hmono)
    (fun i => matrixFiniteRelativeExpectation_nonneg dims V hd U hU (f i) (hpos i)) _
    (matrixFiniteRelativeExpectation_preserves_positive_sup dims V hd U hU f hmono hpos T hT)

theorem matrixFiniteRelativeExpectation_normal (s : Set (MatrixFiniteOperatorAlgebra dims hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB s T) :
    IsLUB (matrixFiniteRelativeExpectation dims V hd U hU '' s) (matrixFiniteRelativeExpectation dims V hd U hU T) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  have h := matrixFiniteRelativeExpectation_preserves_positive_sup dims V hd U hU (fun a : s => a.val)
    (fun _ _ hab => hab) (fun a => hpos a.val a.property) T (hr.symm ▸ hT)
  have he : Set.range (fun a : s => matrixFiniteRelativeExpectation dims V hd U hU a.val) =
      matrixFiniteRelativeExpectation dims V hd U hU '' s := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact he ▸ h

end ThomGame.Analysis
