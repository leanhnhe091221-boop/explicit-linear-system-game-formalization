module

public import ThomGame.Quantum.FinitePOVMStrategy
public import ThomGame.Quantum.FiniteNaimark
public import ThomGame.Quantum.TensorCompression

/-! Enlarging the local dimensions converts every finite POVM strategy to a
projective strategy with exactly the same full correlation table. -/

@[expose] public section
namespace ThomGame.Quantum.FinitePOVMStrategy

open scoped TensorProduct

variable {X Y A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

/-- The state embeddings are fixed independently of both players' questions.
The equality holds for every question pair, including pairs of referee weight zero. -/
theorem exists_projective (S : FinitePOVMStrategy X Y A B) :
    ∃ T : FiniteStrategy X Y A B, T.correlation = S.correlation := by
  letI : NeZero S.dimAlice := ⟨Nat.ne_of_gt S.dimAlice_pos⟩
  letI : NeZero S.dimBob := ⟨Nat.ne_of_gt S.dimBob_pos⟩
  obtain ⟨d, hd, V, P, hP⟩ := POVM.exists_projective_dilation S.alice
  obtain ⟨e, he, W, Q, hQ⟩ := POVM.exists_projective_dilation S.bob
  let T : FiniteStrategy X Y A B := {
    dimAlice := d
    dimBob := e
    dimAlice_pos := hd
    dimBob_pos := he
    state := TensorProduct.mapIsometry V W S.state
    norm_state := (TensorProduct.mapIsometry V W).norm_map S.state |>.trans S.norm_state
    alice := P
    bob := Q }
  refine ⟨T, ?_⟩
  funext x y a b
  rw [show T.correlation x y a b =
    (inner ℂ T.state (TensorProduct.mapL ((P x).proj a) ((Q y).proj b) T.state)).re
      from T.toCommuting.correlation_inner x y a b]
  exact re_inner_tensor_compression_of_inner V W ((P x).proj a) ((Q y).proj b)
    ((S.alice x).effect a) ((S.bob y).effect b) (hP x a) (hQ y b) S.state

theorem isProbabilityTable (S : FinitePOVMStrategy X Y A B) :
    IsProbabilityTable S.correlation := by
  obtain ⟨T, hT⟩ := S.exists_projective
  rw [← hT]
  exact T.isProbabilityTable

theorem noSignalling (S : FinitePOVMStrategy X Y A B) : NoSignalling S.correlation := by
  obtain ⟨T, hT⟩ := S.exists_projective
  rw [← hT]
  exact T.noSignalling

end ThomGame.Quantum.FinitePOVMStrategy
