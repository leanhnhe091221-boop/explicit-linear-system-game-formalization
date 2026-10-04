module

public import ThomGame.Analysis.RelatorAreaCalculus
public import ThomGame.Finite.Words

/-! Soundness of finite word rewriting certificates with an explicit area. -/

@[expose] public section
namespace ThomGame.Analysis

variable {S : Type*} {rels : Set (FreeGroup S)}

def WordRelatorArea (rels : Set (FreeGroup S)) (w : Word S) (N : ℕ) : Prop :=
  ∃ n ≤ N, RelatorArea rels (FreeGroup.mk w) n

namespace WordRelatorArea

variable {w : Word S} {N : ℕ}

theorem inverse (h : WordRelatorArea rels w N) :
    WordRelatorArea rels (Word.inverse w) N := by
  obtain ⟨n, hn, hp⟩ := h
  exact ⟨n, hn, by simpa only [Word.inverse, ← FreeGroup.inv_mk] using hp.inv⟩

theorem rotate (u v : Word S) (h : WordRelatorArea rels (u ++ v) N) :
    WordRelatorArea rels (v ++ u) N := by
  obtain ⟨n, hn, hp⟩ := h
  refine ⟨n, hn, ?_⟩
  have hh := hp.conj (FreeGroup.mk u)⁻¹
  simpa only [← FreeGroup.mul_mk, inv_mul_cancel_left, inv_inv] using hh

theorem split (w : Word S) (h : WordRelatorArea rels w N) (k : ℕ) :
    RelatorEquality rels (FreeGroup.mk (w.take k))
      (FreeGroup.mk (Word.inverse (w.drop k))) N := by
  obtain ⟨n, hn, hp⟩ := h
  refine ⟨n, hn, ?_⟩
  simpa only [Word.inverse, ← FreeGroup.inv_mk, inv_inv, FreeGroup.mul_mk,
    List.take_append_drop] using hp

end WordRelatorArea

/-- Both endpoints are literal words and the proof has an explicit area cap. -/
structure CertifiedWordRule (rels : Set (FreeGroup S)) (N : ℕ) where
  lhs : Word S
  rhs : Word S
  sound : RelatorEquality rels (FreeGroup.mk lhs) (FreeGroup.mk rhs) N

namespace CertifiedWordRule

variable {N : ℕ}

def fromRelator (w : Word S) (h : WordRelatorArea rels w N)
    (reverse : Bool) (rotation split : ℕ) : CertifiedWordRule rels N := by
  let w' := if reverse then Word.inverse w else w
  have h' : WordRelatorArea rels w' N := by
    dsimp [w']
    split_ifs
    · exact h.inverse
    · exact h
  let w'' := w'.drop rotation ++ w'.take rotation
  have h'' : WordRelatorArea rels w'' N :=
    WordRelatorArea.rotate _ _ (by simpa only [List.take_append_drop] using h')
  exact ⟨w''.take split, Word.inverse (w''.drop split), h''.split _ split⟩

/-- A checked edge may freely cancel words on either side of the local rewrite. -/
theorem contextual_sound (R : CertifiedWordRule rels N) (pre post v w : Word S)
    (hv : FreeGroup.mk v = FreeGroup.mk pre * FreeGroup.mk R.lhs * FreeGroup.mk post)
    (hw : FreeGroup.mk w = FreeGroup.mk pre * FreeGroup.mk R.rhs * FreeGroup.mk post) :
    RelatorEquality rels (FreeGroup.mk v) (FreeGroup.mk w) N := by
  rw [hv, hw]
  exact (R.sound.mul_left (FreeGroup.mk pre)).mul_right (FreeGroup.mk post)

end CertifiedWordRule

/-- A replayable trace. Every transition is checked against a certified rule. -/
inductive WordRewriteTrace {N : ℕ} (rules : List (CertifiedWordRule rels N)) :
    Word S → Word S → ℕ → Prop
  | refl (w : Word S) : WordRewriteTrace rules w w 0
  | step {u v w : Word S} {n : ℕ} (R : CertifiedWordRule rels N) (hR : R ∈ rules)
      (pre post : Word S)
      (hu : FreeGroup.mk u = FreeGroup.mk pre * FreeGroup.mk R.lhs * FreeGroup.mk post)
      (hv : FreeGroup.mk v = FreeGroup.mk pre * FreeGroup.mk R.rhs * FreeGroup.mk post)
      (tail : WordRewriteTrace rules v w n) : WordRewriteTrace rules u w (n+1)

theorem WordRewriteTrace.sound {N : ℕ} {rules : List (CertifiedWordRule rels N)}
    {v w : Word S} {n : ℕ} (h : WordRewriteTrace rules v w n) :
    RelatorEquality rels (FreeGroup.mk v) (FreeGroup.mk w) (N*n) := by
  induction h with
  | refl w => exact RelatorEquality.refl _
  | step R _ p s hu hv _ ih =>
      have hh := (R.contextual_sound p s _ _ hu hv).trans ih
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm N] using hh

end ThomGame.Analysis
