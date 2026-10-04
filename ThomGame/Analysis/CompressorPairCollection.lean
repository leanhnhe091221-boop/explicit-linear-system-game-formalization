module

public import ThomGame.Analysis.PrimeFivePairSectionCollection
public import ThomGame.Groups.CompressorCompression

/-! Bounded collection for the actual compressor's adjacent root pair. -/

@[expose] public section
namespace ThomGame.Analysis

open Compressor

theorem compressor_elementary_area (w : Word Compressor.Generator)
    (hw : w ∈ e0 ++ e1 ++ e2e3 ++ e4) :
    RelatorArea Compressor.relators (Word.eval FreeGroup.of w) 1 := by
  have hm : w ∈ rawRelators := by
    simp only [List.mem_append] at hw
    simp only [rawRelators, List.mem_append]
    tauto
  have hh : Word.eval FreeGroup.of w = FreeGroup.mk w := FreeGroup.lift_of_apply _
  rw [hh]
  exact RelatorArea.relator ⟨w, hm, rfl⟩

theorem compressor_e0_area (root : Root) (m : Coeff) :
    RelatorEquality Compressor.relators (FreeGroup.of (.inl (root,m)) ^ 5) 1 1 := by
  have hm : power (X root m) 5 ∈ e0 :=
    List.mem_flatMap.mpr ⟨root, mem_roots root, List.mem_map.mpr ⟨m, mem_coefficients m, rfl⟩⟩
  have hh := compressor_elementary_area _ (by simp only [List.mem_append]; tauto)
  exact ⟨1, le_rfl, by simpa [power, X, pow_succ, mul_assoc] using hh⟩

theorem compressor_e1_area (root s : Root) (m n : Coeff) (hrs : separated root s) :
    RelatorEquality Compressor.relators
      (FreeGroup.of (.inl (root,m)) * FreeGroup.of (.inl (s,n)))
      (FreeGroup.of (.inl (s,n)) * FreeGroup.of (.inl (root,m))) 1 := by
  have hm : Word.commutator (X root m) (X s n) ∈ e1 := by
    apply List.mem_flatMap.mpr
    refine ⟨root, mem_roots root, List.mem_flatMap.mpr ⟨s, mem_roots s, ?_⟩⟩
    simp only [hrs, ite_true]
    exact List.mem_flatMap.mpr ⟨m, mem_coefficients m, List.mem_map.mpr ⟨n, mem_coefficients n, rfl⟩⟩
  have hh := compressor_elementary_area _ (by simp only [List.mem_append]; tauto)
  exact ⟨1, le_rfl, by simpa [X, mul_inv_rev, mul_assoc] using hh⟩

theorem compressor_e4_area (root s : Root) (m n l : Coeff) (hrs : separated (across root) s) :
    RelatorEquality Compressor.relators
      ((FreeGroup.of (.inl (root,m)) * FreeGroup.of (.inl (right root,n)) *
        (FreeGroup.of (.inl (root,m)))⁻¹ * (FreeGroup.of (.inl (right root,n)))⁻¹) *
        FreeGroup.of (.inl (s,l)))
      (FreeGroup.of (.inl (s,l)) *
        (FreeGroup.of (.inl (root,m)) * FreeGroup.of (.inl (right root,n)) *
          (FreeGroup.of (.inl (root,m)))⁻¹ * (FreeGroup.of (.inl (right root,n)))⁻¹)) 1 := by
  have hm : Word.commutator (Word.commutator (X root m) (X (right root) n)) (X s l) ∈ e4 := by
    apply List.mem_flatMap.mpr
    refine ⟨root, mem_roots root, List.mem_flatMap.mpr ⟨s, mem_roots s, ?_⟩⟩
    simp only [hrs, ite_true]
    exact List.mem_flatMap.mpr ⟨m, mem_coefficients m,
      List.mem_flatMap.mpr ⟨n, mem_coefficients n, List.mem_map.mpr ⟨l, mem_coefficients l, rfl⟩⟩⟩
  have hh := compressor_elementary_area _ (by simp only [List.mem_append]; tauto)
  exact ⟨1, le_rfl, by simpa [X, mul_inv_rev, mul_assoc] using hh⟩

theorem compressorPair_collection_relations {r : ℕ} (root : Root) (σ : Fin r → Coeff) :
    PairCollectionRelations Compressor.relators
      (fun i => FreeGroup.of (.inl (root,σ i))) (fun j => FreeGroup.of (.inl (right root,σ j))) where
  a_fifth i := compressor_e0_area root (σ i)
  b_fifth i := compressor_e0_area (right root) (σ i)
  aa i j := compressor_e1_area root root (σ i) (σ j) ⟨root.property,root.property⟩
  bb i j := compressor_e1_area (right root) (right root) (σ i) (σ j)
    ⟨(right root).property,(right root).property⟩
  ca p i := compressor_e4_area root root (σ p.1) (σ p.2) (σ i)
    ⟨root.property, (third_ne_source root).symm⟩
  cb p i := compressor_e4_area root (right root) (σ p.1) (σ p.2) (σ i)
    ⟨(third_ne_source root).symm,(third_ne_target root).symm⟩

def compressorPairCanonical {r : ℕ} (root : Root) (σ : Fin r → Coeff)
    (g : FinitePrimeFivePair r) : FreeGroup Compressor.Generator :=
  PairCollectionRelations.normal
    (fun i => FreeGroup.of (.inl (root,σ i))) (fun j => FreeGroup.of (.inl (right root,σ j))) g

@[simp] theorem compressorPairCanonical_one {r : ℕ} (root : Root) (σ : Fin r → Coeff) :
    compressorPairCanonical root σ (1 : FinitePrimeFivePair r) = 1 :=
  (compressorPair_collection_relations root σ).normal_one

theorem compressorPairCanonical_mul_area {r : ℕ} (root : Root) (σ : Fin r → Coeff)
    (hr : r ≤ 7) (g k : FinitePrimeFivePair r) :
    RelatorEquality Compressor.relators
      (compressorPairCanonical root σ g * compressorPairCanonical root σ k)
      (compressorPairCanonical root σ (g*k)) 1000000000 :=
  (compressorPair_collection_relations root σ).normal_mul hr g k

theorem compressorPairCanonical_inv_area {r : ℕ} (root : Root) (σ : Fin r → Coeff)
    (hr : r ≤ 7) (g : FinitePrimeFivePair r) :
    RelatorEquality Compressor.relators
      (compressorPairCanonical root σ g⁻¹) (compressorPairCanonical root σ g)⁻¹ 1000000000 :=
  (compressorPair_collection_relations root σ).normal_inv hr g

end ThomGame.Analysis
