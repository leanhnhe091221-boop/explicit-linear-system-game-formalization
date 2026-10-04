module

public import ThomGame.Certificates.NetzerThomResidual
public import ThomGame.Certificates.NetzerThomNumericBounds

@[expose] public section
namespace ThomGame.Certificates.NetzerThom

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem residualClass_pair_bounds {c : ResidualClass} (hc : c ∈ residualClasses)
    {ij : ℕ × ℕ} (hij : ij ∈ c.pairs) : ij.1 < 121 ∧ ij.2 < 121 := by
  have h := (List.all_eq_true.mp residualClasses_shape) c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.1.2 ij hij

theorem residualClass_term_bounds {c : ResidualClass} (hc : c ∈ residualClasses)
    {i : ℕ} (hi : i ∈ c.terms) : i < 182 := by
  have h := (List.all_eq_true.mp residualClasses_shape) c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2 i hi

theorem residualClass_word_length {c : ResidualClass} (hc : c ∈ residualClasses) :
    c.representative.length ≤ 4 := by
  have h := (List.all_eq_true.mp residualClasses_shape) c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.1.1.1

def decodePair (n : ℕ) : ℕ × ℕ := (n / 121,n % 121)

theorem decodePair_encode {i j : ℕ} (hj : j < 121) :
    decodePair (i * 121 + j) = (i,j) := by
  simp [decodePair, Nat.add_div, Nat.add_mod, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, hj]

theorem decoded_range : (List.range (121 * 121)).map decodePair =
    (List.range 121).flatMap (fun i => (List.range 121).map (fun j => (i,j))) := by rfl

theorem gramPairs_decode : gramPairIndices.map decodePair =
    residualClasses.flatMap ResidualClass.pairs := by
  simp only [gramPairIndices, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro c hc
  have hh : ∀ ij ∈ c.pairs, decodePair (ij.1 * 121 + ij.2) = ij := by
    intro ij hij
    exact decodePair_encode (residualClass_pair_bounds hc hij).2
  change c.pairs.map (fun p => decodePair (p.1 * 121 + p.2)) = c.pairs
  calc
    _ = c.pairs.map id := List.map_congr_left hh
    _ = c.pairs := List.map_id _

theorem gramPairs_partition :
    (residualClasses.flatMap ResidualClass.pairs).Perm
      ((List.range 121).flatMap (fun i => (List.range 121).map (fun j => (i,j)))) := by
  rw [← gramPairs_decode, ← decoded_range]
  exact gramPairIndices_partition.map decodePair

end ThomGame.Certificates.NetzerThom
