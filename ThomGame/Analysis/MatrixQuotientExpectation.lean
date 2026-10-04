module

public import ThomGame.Analysis.MatrixSequenceExpectation
public import ThomGame.Analysis.MatrixTraceMetric

/-!
# Coordinate expectations descend to the tracial quotient

The resulting linear projection has precisely the prescribed internal
subalgebra as its range. It is unital, star preserving, bimodular, and
preserves the actual ultralimit trace and its pairings.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat)
  (S : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
  (hd : ∀ i, 0 < dims i) (L : Filter ι)

noncomputable def matrixQuotientExpectation :
    MatrixTracialQuotient dims L →ₗ[ℂ] MatrixTracialQuotient dims L where
  toFun := Quotient.lift (fun A => matrixQuotientMk dims L (matrixSequenceExpectation dims S hd A)) (by
    intro A B h
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact matrixSequenceExpectation_null dims S hd L (A - B) ((Submodule.quotientRel_def _).mp h))
  map_add' x y := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    obtain ⟨B, rfl⟩ := matrixQuotientMk_surjective dims L y
    change matrixQuotientMk dims L (matrixSequenceExpectation dims S hd (A + B)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
    change matrixQuotientMk dims L (matrixSequenceExpectation dims S hd (c • A)) = _
    rw [map_smul]
    exact (matrixQuotientStarAlgHom dims L).toAlgHom.toLinearMap.map_smul c _

@[simp] theorem matrixQuotientExpectation_mk (A : BoundedMatrixSequence dims) :
    matrixQuotientExpectation dims S hd L (matrixQuotientMk dims L A) =
      matrixQuotientMk dims L (matrixSequenceExpectation dims S hd A) := rfl

theorem matrixQuotientExpectation_mem (x : MatrixTracialQuotient dims L) :
    matrixQuotientExpectation dims S hd L x ∈ matrixInternalQuotient dims S L := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  exact ⟨matrixSequenceExpectation dims S hd A, matrixSequenceExpectation_mem dims S hd A, rfl⟩

theorem matrixQuotientExpectation_eq_self (x : MatrixTracialQuotient dims L)
    (hx : x ∈ matrixInternalQuotient dims S L) : matrixQuotientExpectation dims S hd L x = x := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims S L x).mp hx
  rw [matrixQuotientExpectation_mk, matrixSequenceExpectation_eq_self dims S hd A hA]

theorem matrixQuotientExpectation_eq_self_iff (x : MatrixTracialQuotient dims L) :
    matrixQuotientExpectation dims S hd L x = x ↔ x ∈ matrixInternalQuotient dims S L :=
  ⟨fun h => h ▸ matrixQuotientExpectation_mem dims S hd L x,
    matrixQuotientExpectation_eq_self dims S hd L x⟩

theorem matrixQuotientExpectation_range :
    LinearMap.range (matrixQuotientExpectation dims S hd L) =
      (matrixInternalQuotient dims S L).toSubalgebra.toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact matrixQuotientExpectation_mem dims S hd L y
  · intro hx
    exact ⟨x, matrixQuotientExpectation_eq_self dims S hd L x hx⟩

@[simp] theorem matrixQuotientExpectation_one : matrixQuotientExpectation dims S hd L 1 = 1 :=
  matrixQuotientExpectation_eq_self dims S hd L 1 (matrixInternalQuotient dims S L).one_mem

@[simp] theorem matrixQuotientExpectation_idem (x : MatrixTracialQuotient dims L) :
    matrixQuotientExpectation dims S hd L (matrixQuotientExpectation dims S hd L x) =
      matrixQuotientExpectation dims S hd L x :=
  matrixQuotientExpectation_eq_self dims S hd L _ (matrixQuotientExpectation_mem dims S hd L x)

@[simp] theorem matrixQuotientExpectation_star (x : MatrixTracialQuotient dims L) :
    matrixQuotientExpectation dims S hd L (star x) =
      star (matrixQuotientExpectation dims S hd L x) := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims L x
  simp only [matrixQuotientMk_star, matrixQuotientExpectation_mk, matrixSequenceExpectation_star]

theorem matrixQuotientExpectation_mul_left (a x : MatrixTracialQuotient dims L)
    (ha : a ∈ matrixInternalQuotient dims S L) :
    matrixQuotientExpectation dims S hd L (a * x) = a * matrixQuotientExpectation dims S hd L x := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims S L a).mp ha
  obtain ⟨X, rfl⟩ := matrixQuotientMk_surjective dims L x
  rw [← map_mul, matrixQuotientExpectation_mk, matrixSequenceExpectation_mul_left dims S hd A X hA,
    map_mul, matrixQuotientExpectation_mk]

theorem matrixQuotientExpectation_mul_right (x a : MatrixTracialQuotient dims L)
    (ha : a ∈ matrixInternalQuotient dims S L) :
    matrixQuotientExpectation dims S hd L (x * a) = matrixQuotientExpectation dims S hd L x * a := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims S L a).mp ha
  obtain ⟨X, rfl⟩ := matrixQuotientMk_surjective dims L x
  rw [← map_mul, matrixQuotientExpectation_mk, matrixSequenceExpectation_mul_right dims S hd X A hA,
    map_mul, matrixQuotientExpectation_mk]

theorem matrixQuotientExpectation_bimodule (a x b : MatrixTracialQuotient dims L)
    (ha : a ∈ matrixInternalQuotient dims S L) (hb : b ∈ matrixInternalQuotient dims S L) :
    matrixQuotientExpectation dims S hd L (a * x * b) =
      a * matrixQuotientExpectation dims S hd L x * b := by
  rw [matrixQuotientExpectation_mul_right dims S hd L _ b hb,
    matrixQuotientExpectation_mul_left dims S hd L a x ha]

variable (U : Ultrafilter ι)

theorem matrixQuotientExpectation_trace (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace dims hd U (matrixQuotientExpectation dims S hd (U : Filter ι) x) =
      matrixUltratrace dims hd U x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact matrixSequenceExpectation_ultratrace dims S hd U A

theorem matrixQuotientExpectation_pairing (x b : MatrixTracialQuotient dims (U : Filter ι))
    (hb : b ∈ matrixInternalQuotient dims S (U : Filter ι)) :
    matrixUltratrace dims hd U (star b * matrixQuotientExpectation dims S hd (U : Filter ι) x) =
      matrixUltratrace dims hd U (star b * x) := by
  obtain ⟨B, hB, rfl⟩ := (mem_matrixInternalQuotient dims S (U : Filter ι) b).mp hb
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  rw [matrixQuotientMk_star, matrixQuotientExpectation_mk, ← map_mul, ← map_mul]
  exact matrixSequenceExpectation_pairing dims S hd U A B hB

theorem matrixQuotientExpectation_unique (x z : MatrixTracialQuotient dims (U : Filter ι))
    (hz : z ∈ matrixInternalQuotient dims S (U : Filter ι))
    (hpair : ∀ b ∈ matrixInternalQuotient dims S (U : Filter ι),
      matrixUltratrace dims hd U (star b * z) = matrixUltratrace dims hd U (star b * x)) :
    matrixQuotientExpectation dims S hd (U : Filter ι) x = z := by
  apply sub_eq_zero.mp
  apply (matrixUltratrace_faithful dims hd U _).mp
  let b := matrixQuotientExpectation dims S hd (U : Filter ι) x - z
  have hb : b ∈ matrixInternalQuotient dims S (U : Filter ι) :=
    (matrixInternalQuotient dims S (U : Filter ι)).sub_mem
      (matrixQuotientExpectation_mem dims S hd (U : Filter ι) x) hz
  change matrixUltratrace dims hd U (star b * (matrixQuotientExpectation dims S hd (U : Filter ι) x - z)) = 0
  rw [mul_sub]
  change matrixUltratraceLinear dims hd U (_ - _) = 0
  rw [map_sub]
  change matrixUltratrace dims hd U (star b * matrixQuotientExpectation dims S hd (U : Filter ι) x) -
    matrixUltratrace dims hd U (star b * z) = 0
  rw [matrixQuotientExpectation_pairing dims S hd U x b hb, hpair b hb, sub_self]

theorem matrixQuotientExpectation_hilbertNorm_le (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixHilbertEmbedding dims hd U (matrixQuotientExpectation dims S hd (U : Filter ι) x)‖ ≤
      ‖matrixHilbertEmbedding dims hd U x‖ := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  exact le_of_tendsto_of_tendsto
    (matrixHilbertEmbedding_norm_tendsto dims hd U (matrixSequenceExpectation dims S hd A))
    (matrixHilbertEmbedding_norm_tendsto dims hd U A)
    (Eventually.of_forall (matrixSequenceExpectation_hsNorm_le dims S hd A))

end ThomGame.Analysis
