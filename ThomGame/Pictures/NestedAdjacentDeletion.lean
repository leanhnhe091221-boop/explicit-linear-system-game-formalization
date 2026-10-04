module

public import ThomGame.Pictures.CircularSubsets
public import ThomGame.Pictures.ReturnTransport
public import ThomGame.Pictures.ReturnSurgery

/-!
# Adjacent deletion within an already restricted circle

The concrete increasing enumeration lets the numbered-circle theorem
act on any previously retained subset. Flattening nested returns and
commuting retained target exchanges recover the actual full permutation.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

open Equiv MarkedReturn CycleSurgery

variable {A : Type*} [Finite A] [DecidableEq A] {m n : Nat}

/-- Transport adjacent deletion along an explicit numbering of the
ambient circle. -/
theorem OrderedNoncrossing.splice_restrict_numbered
    {c f : Perm A} {o : A → A → A → Prop} (h : OrderedNoncrossing c o f)
    (e : Fin m ≃ A) (hc : ∀ i, c (e i) = e (finRotate m i))
    (ho : ∀ i j k, o (e i) (e j) (e k) ↔ sbtw i j k)
    (a : A) (p : A → Prop) (ha : ¬ p a) (hb : ¬ p (c a)) :
    OrderedNoncrossing (perm c p) (fun x y z : Subtype p => o x.val y.val z.val)
      (perm (splice f a (c a)) p) := by
  let f' : Perm (Fin m) := (e.trans f).trans e.symm
  have hf : ∀ i, f (e i) = e (f' i) := by intro i; simp [f']
  have hn : OrderedNoncrossing (finRotate m) sbtw f' := by
    apply h.transport e.symm
    · intro x
      simpa only [e.apply_symm_apply, e.symm_apply_apply] using
        (congrArg e.symm (hc (e.symm x))).symm
    · intro x
      simp [f']
    · intro x y z
      simpa only [e.apply_symm_apply] using (ho (e.symm x) (e.symm y) (e.symm z)).symm
  let p' := fun i => p (e i)
  have hae : e (e.symm a) = a := e.apply_symm_apply a
  have hbe : e (finRotate m (e.symm a)) = c a := by rw [← hc, hae]
  have hs := hn.splice_restrict_adjacent (e.symm a) p'
    (by simpa only [p', hae] using ha) (by simpa only [p', hbe] using hb)
  let E : Subtype p' ≃ Subtype p := e.subtypeEquiv (fun _ => Iff.rfl)
  have hg : ∀ i, splice f a (c a) (e i) =
      e (splice f' (e.symm a) (finRotate m (e.symm a)) i) := by
    intro i
    simp only [splice_apply]
    rw [e.injective.map_swap, hae, hbe, ← hf]
  apply hs.transport E
  · exact perm_subtypeEquiv (finRotate m) c e hc p' p (fun _ => Iff.rfl)
  · exact perm_subtypeEquiv _ _ e hg p' p (fun _ => Iff.rfl)
  · intro x y z
    exact ho x.val y.val z.val

/-- The next seam is adjacent in the retained circle. Its exchange and
deletion can be performed there, while the conclusion uses first return
of the original permutation with that actual target exchange. -/
theorem OrderedNoncrossing.splice_restrict_nested
    {f : Perm (Fin n)} (p q : Fin n → Prop) (hqp : ∀ x, q x → p x)
    (h : OrderedNoncrossing (perm (finRotate n) p)
      (fun x y z : Subtype p => sbtw x.val y.val z.val) (perm f p))
    (a b : Subtype p) (hc : perm (finRotate n) p a = b)
    (ha : ¬ q a.val) (hb : ¬ q b.val) :
    OrderedNoncrossing (perm (finRotate n) q)
      (fun x y z : Subtype q => sbtw x.val y.val z.val)
      (perm (splice f a.val b.val) q) := by
  classical
  let e := (subsetEnumeration p).toEquiv
  have hs := h.splice_restrict_numbered e (subsetEnumeration_return p)
    (strictMono_sbtw _ (subsetEnumeration_strictMono p)) a
    (fun x : Subtype p => q x.val) ha (by simpa only [hc] using hb)
  rw [hc, ← perm_splice_retained f p a b] at hs
  apply hs.transport (nestedSubset p q hqp)
  · exact perm_nested_subset (finRotate n) p q hqp
  · exact perm_nested_subset (splice f a.val b.val) p q hqp
  · intro x y z
    rfl

end ThomGame.Pictures.CircularPartition
