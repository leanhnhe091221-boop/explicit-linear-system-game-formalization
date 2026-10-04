module

public import ThomGame.Analysis.WeakClosedPositiveSuprema
public import ThomGame.Analysis.MatrixFiniteTraceGeometry

/-!
# Positive monotone completeness and normality of the matrix trace

The concrete generated matrix algebra has actual positive directed
suprema. Its faithful matrix trace preserves these suprema, both in
the complex order and after taking real parts. The assertions apply to
arbitrary directed index sets and arbitrary matrix index ultrafilters.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology ComplexOrder

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

theorem matrixOperatorAlgebra_wot_isClosed :
    IsClosed {T : MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U |
      T.toCLM ∈ matrixOperatorAlgebra dims hd U} := by
  change IsClosed (matrixWOTAlgebra dims hd U :
    Set (MatrixTraceHilbert dims hd U →WOT[ℂ] MatrixTraceHilbert dims hd U))
  exact matrixWOTAlgebra_isClosed dims hd U

variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

theorem exists_matrixFinite_positive_sup (f : κ → MatrixFiniteOperatorAlgebra dims hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i) (hbound : BddAbove (Set.range f)) :
    ∃ T : MatrixFiniteOperatorAlgebra dims hd U, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      (∀ x, Tendsto (fun i => (f i).val x) atTop (𝓝 (T.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val)) :=
  exists_positive_sup_in_wot_closed_subalgebra (matrixOperatorAlgebra dims hd U)
    (matrixOperatorAlgebra_wot_isClosed dims hd U) f hmono hpos hbound

theorem matrixFinite_positive_tendsto_sup (f : κ → MatrixFiniteOperatorAlgebra dims hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    (∀ x, Tendsto (fun i => (f i).val x) atTop (𝓝 (T.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val)) :=
  positive_family_tendsto_sup_in_wot_closed_subalgebra (matrixOperatorAlgebra dims hd U)
    (matrixOperatorAlgebra_wot_isClosed dims hd U) f hmono hpos T hT

theorem matrixFiniteTrace_preserves_positive_sup (f : κ → MatrixFiniteOperatorAlgebra dims hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixFiniteTrace dims hd U (f i))) (matrixFiniteTrace dims hd U T) := by
  apply isLUB_of_tendsto_atTop ((matrixFiniteTrace_monotone dims hd U).comp hmono)
  exact matrixFiniteTrace_wot_tendsto dims hd U (matrixFinite_positive_tendsto_sup dims hd U f hmono hpos T hT).2

theorem matrixFiniteRealTrace_preserves_positive_sup (f : κ → MatrixFiniteOperatorAlgebra dims hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixFiniteRealTrace dims hd U (f i))) (matrixFiniteRealTrace dims hd U T) := by
  apply isLUB_of_tendsto_atTop
    (fun i j hij => (matrixFiniteTrace_monotone dims hd U (hmono hij)).1)
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (matrixFiniteTrace_wot_tendsto dims hd U (matrixFinite_positive_tendsto_sup dims hd U f hmono hpos T hT).2)

theorem matrixFiniteRealTrace_sup_eq_ciSup (f : κ → MatrixFiniteOperatorAlgebra dims hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB (Set.range f) T) :
    matrixFiniteRealTrace dims hd U T = ⨆ i, matrixFiniteRealTrace dims hd U (f i) :=
  (matrixFiniteRealTrace_preserves_positive_sup dims hd U f hmono hpos T hT).ciSup_eq.symm

theorem exists_matrixFinite_directed_positive_sup (s : Set (MatrixFiniteOperatorAlgebra dims hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a) (hbound : BddAbove s) :
    ∃ T : MatrixFiniteOperatorAlgebra dims hd U, IsLUB s T :=
  exists_directed_positive_sup_in_wot_closed_subalgebra (matrixOperatorAlgebra dims hd U)
    (matrixOperatorAlgebra_wot_isClosed dims hd U) s hs hdir hpos hbound

theorem exists_matrixFinite_directed_sup (s : Set (MatrixFiniteOperatorAlgebra dims hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hbound : BddAbove s) :
    ∃ T : MatrixFiniteOperatorAlgebra dims hd U, IsLUB s T :=
  exists_directed_sup_in_wot_closed_subalgebra (matrixOperatorAlgebra dims hd U)
    (matrixOperatorAlgebra_wot_isClosed dims hd U) s hs hdir hbound

theorem matrixFiniteTrace_normal (s : Set (MatrixFiniteOperatorAlgebra dims hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a)
    (T : MatrixFiniteOperatorAlgebra dims hd U) (hT : IsLUB s T) :
    IsLUB (matrixFiniteTrace dims hd U '' s) (matrixFiniteTrace dims hd U T) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  have ht := matrixFiniteTrace_preserves_positive_sup dims hd U (fun a : s => a.val)
    (fun _ _ h => h) (fun a => hpos a.val a.property) T (hr.symm ▸ hT)
  have he : Set.range (fun a : s => matrixFiniteTrace dims hd U a.val) = matrixFiniteTrace dims hd U '' s := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact he ▸ ht

end ThomGame.Analysis
