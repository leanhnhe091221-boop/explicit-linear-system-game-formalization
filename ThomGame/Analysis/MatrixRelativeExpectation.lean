module

public import ThomGame.Analysis.MatrixRelativeCommutant

/-!
# The actual relative-commutant expectation on the tracial quotient

The mean ergodic projection of a bounded trace vector has a unique
bounded algebra representative. This defines a linear, unital,
trace-preserving, star-preserving bimodule projection onto the actual
relative commutant, with the exact operator norm contraction bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable (dims : Nat → Nat) {h : Nat} [NeZero h]
  (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

noncomputable def matrixRelativeProjectionElement (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    MatrixTracialQuotient dims (L : Filter Nat) :=
  Classical.choose (exists_matrixMarkovProjection_element dims U hd L hL x)

theorem matrixRelativeProjectionElement_spec (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixHilbertEmbedding dims hd L (matrixRelativeProjectionElement dims U hd L hL x) =
        matrixMarkovProjection dims U hd L (matrixHilbertEmbedding dims hd L x) ∧
      matrixQuotientLazyMarkov dims U hd (L : Filter Nat) (matrixRelativeProjectionElement dims U hd L hL x) =
        matrixRelativeProjectionElement dims U hd L hL x ∧
      ‖matrixLeftRepresentation dims hd L (matrixRelativeProjectionElement dims U hd L hL x)‖ ≤
        ‖matrixLeftRepresentation dims hd L x‖ :=
  Classical.choose_spec (exists_matrixMarkovProjection_element dims U hd L hL x)

noncomputable def matrixRelativeExpectation :
    MatrixTracialQuotient dims (L : Filter Nat) →ₗ[ℂ] MatrixTracialQuotient dims (L : Filter Nat) where
  toFun := matrixRelativeProjectionElement dims U hd L hL
  map_add' x y := by
    apply matrixHilbertEmbedding_injective dims hd L
    simp only [(matrixRelativeProjectionElement_spec dims U hd L hL _).1, map_add]
  map_smul' c x := by
    apply matrixHilbertEmbedding_injective dims hd L
    simp only [(matrixRelativeProjectionElement_spec dims U hd L hL _).1, map_smul, RingHom.id_apply]

@[simp] theorem matrixRelativeExpectation_embedding (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixHilbertEmbedding dims hd L (matrixRelativeExpectation dims U hd L hL x) =
      matrixMarkovProjection dims U hd L (matrixHilbertEmbedding dims hd L x) :=
  (matrixRelativeProjectionElement_spec dims U hd L hL x).1

theorem matrixRelativeExpectation_mem (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL x ∈ matrixRelativeCommutant dims U (L : Filter Nat) :=
  (matrixQuotientLazyMarkov_fixed_iff_mem dims U hd L _).mp
    (matrixRelativeProjectionElement_spec dims U hd L hL x).2.1

theorem matrixRelativeExpectation_operatorNorm_le (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixLeftRepresentation dims hd L (matrixRelativeExpectation dims U hd L hL x)‖ ≤
      ‖matrixLeftRepresentation dims hd L x‖ :=
  (matrixRelativeProjectionElement_spec dims U hd L hL x).2.2

theorem matrixRelativeExpectation_eq_self (x : MatrixTracialQuotient dims (L : Filter Nat))
    (hx : x ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL x = x := by
  apply matrixHilbertEmbedding_injective dims hd L
  rw [matrixRelativeExpectation_embedding, matrixMarkovProjection_eq_self_iff,
    UniformMatrixMap.hilbertMap_embedding]
  change matrixHilbertEmbedding dims hd L (matrixQuotientLazyMarkov dims U hd (L : Filter Nat) x) = _
  rw [(matrixQuotientLazyMarkov_fixed_iff_mem dims U hd L x).mpr hx]

theorem matrixRelativeExpectation_eq_self_iff (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL x = x ↔
      x ∈ matrixRelativeCommutant dims U (L : Filter Nat) :=
  ⟨fun he => he ▸ matrixRelativeExpectation_mem dims U hd L hL x,
    matrixRelativeExpectation_eq_self dims U hd L hL x⟩

theorem matrixRelativeExpectation_range :
    LinearMap.range (matrixRelativeExpectation dims U hd L hL) =
      (matrixRelativeCommutant dims U (L : Filter Nat)).toSubalgebra.toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact matrixRelativeExpectation_mem dims U hd L hL y
  · intro hx
    exact ⟨x, matrixRelativeExpectation_eq_self dims U hd L hL x hx⟩

@[simp] theorem matrixRelativeExpectation_one : matrixRelativeExpectation dims U hd L hL 1 = 1 :=
  matrixRelativeExpectation_eq_self dims U hd L hL 1 (matrixRelativeCommutant dims U (L : Filter Nat)).one_mem

@[simp] theorem matrixRelativeExpectation_idem (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL (matrixRelativeExpectation dims U hd L hL x) =
      matrixRelativeExpectation dims U hd L hL x :=
  matrixRelativeExpectation_eq_self dims U hd L hL _ (matrixRelativeExpectation_mem dims U hd L hL x)

theorem matrixRelativeExpectation_pairing (x b : MatrixTracialQuotient dims (L : Filter Nat))
    (hb : b ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    matrixUltratrace dims hd L (star b * matrixRelativeExpectation dims U hd L hL x) =
      matrixUltratrace dims hd L (star b * x) := by
  have he := (matrixRelativeCommutantTraceSubspace dims U hd L).inner_starProjection_left_eq_right
    (matrixHilbertEmbedding dims hd L b) (matrixHilbertEmbedding dims hd L x)
  rw [(matrixRelativeCommutantTraceSubspace dims U hd L).starProjection_eq_self_iff.mpr
    (matrixHilbertEmbedding_mem_relativeCommutantTraceSubspace dims U hd L b hb),
    ← matrixMarkovProjection_eq_relativeCommutantProjection dims U hd L hL,
    ← matrixRelativeExpectation_embedding, matrixHilbertEmbedding_inner, matrixHilbertEmbedding_inner] at he
  exact he.symm

theorem matrixRelativeExpectation_trace (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixUltratrace dims hd L (matrixRelativeExpectation dims U hd L hL x) = matrixUltratrace dims hd L x := by
  simpa only [star_one, one_mul] using matrixRelativeExpectation_pairing dims U hd L hL x 1
    (matrixRelativeCommutant dims U (L : Filter Nat)).one_mem

theorem matrixRelativeExpectation_unique (x z : MatrixTracialQuotient dims (L : Filter Nat))
    (hz : z ∈ matrixRelativeCommutant dims U (L : Filter Nat))
    (hpair : ∀ b ∈ matrixRelativeCommutant dims U (L : Filter Nat),
      matrixUltratrace dims hd L (star b * z) = matrixUltratrace dims hd L (star b * x)) :
    matrixRelativeExpectation dims U hd L hL x = z := by
  apply sub_eq_zero.mp
  apply (matrixUltratrace_faithful dims hd L _).mp
  let b := matrixRelativeExpectation dims U hd L hL x - z
  have hb : b ∈ matrixRelativeCommutant dims U (L : Filter Nat) :=
    (matrixRelativeCommutant dims U (L : Filter Nat)).sub_mem
      (matrixRelativeExpectation_mem dims U hd L hL x) hz
  change matrixUltratrace dims hd L (star b * (matrixRelativeExpectation dims U hd L hL x - z)) = 0
  rw [mul_sub]
  change matrixUltratraceLinear dims hd L (_ - _) = 0
  rw [map_sub]
  change matrixUltratrace dims hd L (star b * matrixRelativeExpectation dims U hd L hL x) -
    matrixUltratrace dims hd L (star b * z) = 0
  rw [matrixRelativeExpectation_pairing dims U hd L hL x b hb, hpair b hb, sub_self]

@[simp] theorem matrixRelativeExpectation_star (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL (star x) = star (matrixRelativeExpectation dims U hd L hL x) := by
  apply matrixRelativeExpectation_unique dims U hd L hL
  · exact (matrixRelativeCommutant dims U (L : Filter Nat)).star_mem'
      (matrixRelativeExpectation_mem dims U hd L hL x)
  · intro b hb
    have hp := matrixRelativeExpectation_pairing dims U hd L hL x (star b)
      ((matrixRelativeCommutant dims U (L : Filter Nat)).star_mem' hb)
    simp only [star_star] at hp
    have he := congrArg star hp
    simp only [← matrixUltratrace_star, star_mul] at he
    rw [matrixUltratrace_mul_comm dims hd L (star b),
      matrixUltratrace_mul_comm dims hd L (star b)]
    exact he

theorem matrixRelativeExpectation_mul_left (a x : MatrixTracialQuotient dims (L : Filter Nat))
    (ha : a ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL (a * x) = a * matrixRelativeExpectation dims U hd L hL x := by
  apply matrixRelativeExpectation_unique dims U hd L hL
  · exact (matrixRelativeCommutant dims U (L : Filter Nat)).mul_mem ha
      (matrixRelativeExpectation_mem dims U hd L hL x)
  · intro b hb
    have hp := matrixRelativeExpectation_pairing dims U hd L hL x (star a * b)
      ((matrixRelativeCommutant dims U (L : Filter Nat)).mul_mem
        ((matrixRelativeCommutant dims U (L : Filter Nat)).star_mem' ha) hb)
    simpa only [star_mul, star_star, mul_assoc] using hp

theorem matrixRelativeExpectation_mul_right (x a : MatrixTracialQuotient dims (L : Filter Nat))
    (ha : a ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL (x * a) = matrixRelativeExpectation dims U hd L hL x * a := by
  have he := matrixRelativeExpectation_mul_left dims U hd L hL (star a) (star x)
    ((matrixRelativeCommutant dims U (L : Filter Nat)).star_mem' ha)
  have hs := congrArg star he
  simpa only [← matrixRelativeExpectation_star, star_mul, star_star] using hs

theorem matrixRelativeExpectation_bimodule (a x b : MatrixTracialQuotient dims (L : Filter Nat))
    (ha : a ∈ matrixRelativeCommutant dims U (L : Filter Nat))
    (hb : b ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    matrixRelativeExpectation dims U hd L hL (a * x * b) = a * matrixRelativeExpectation dims U hd L hL x * b := by
  rw [matrixRelativeExpectation_mul_right dims U hd L hL _ b hb,
    matrixRelativeExpectation_mul_left dims U hd L hL a x ha]

theorem matrixRelativeExpectation_hilbertNorm_le (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L (matrixRelativeExpectation dims U hd L hL x)‖ ≤
      ‖matrixHilbertEmbedding dims hd L x‖ := by
  rw [matrixRelativeExpectation_embedding]
  exact ((matrixMarkovProjection dims U hd L).le_opNorm _).trans
    (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (matrixMarkovProjection_norm_le dims U hd L) (norm_nonneg (matrixHilbertEmbedding dims hd L x)))

theorem matrixRelativeExpectation_pythagoras (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L x‖ ^ 2 =
      ‖matrixHilbertEmbedding dims hd L (matrixRelativeExpectation dims U hd L hL x)‖ ^ 2 +
      ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ^ 2 := by
  have he := Submodule.norm_sq_eq_add_norm_sq_starProjection
    (matrixHilbertEmbedding dims hd L x) (matrixRelativeCommutantTraceSubspace dims U hd L)
  rw [Submodule.starProjection_orthogonal_val,
    ← matrixMarkovProjection_eq_relativeCommutantProjection dims U hd L hL,
    ← matrixRelativeExpectation_embedding] at he
  simpa only [map_sub] using he

theorem matrixRelativeExpectation_residualNorm_le (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ≤
      ‖matrixHilbertEmbedding dims hd L x‖ := by
  have he := matrixRelativeExpectation_pythagoras dims U hd L hL x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖matrixHilbertEmbedding dims hd L (matrixRelativeExpectation dims U hd L hL x)‖]

theorem matrixRelativeExpectation_bestApproximation (x b : MatrixTracialQuotient dims (L : Filter Nat))
    (hb : b ∈ matrixRelativeCommutant dims U (L : Filter Nat)) :
    ‖matrixHilbertEmbedding dims hd L (x - matrixRelativeExpectation dims U hd L hL x)‖ ≤
      ‖matrixHilbertEmbedding dims hd L (x - b)‖ := by
  have he := matrixRelativeExpectation_residualNorm_le dims U hd L hL (x - b)
  rw [(matrixRelativeExpectation dims U hd L hL).map_sub,
    matrixRelativeExpectation_eq_self dims U hd L hL b hb] at he
  simpa only [sub_sub_sub_cancel_right] using he

theorem matrixRelativeExpectation_cesaro_tendsto (x : MatrixTracialQuotient dims (L : Filter Nat)) :
    Tendsto (fun n => birkhoffAverage ℂ ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L)
      _root_.id n (matrixHilbertEmbedding dims hd L x)) atTop
      (𝓝 (matrixHilbertEmbedding dims hd L (matrixRelativeExpectation dims U hd L hL x))) := by
  rw [matrixRelativeExpectation_embedding]
  exact meanProjection_tendsto _
    (matrixUniformMarkovPower_hilbertNorm_le dims U hd (fun _ => 1) L) _

end ThomGame.Analysis
