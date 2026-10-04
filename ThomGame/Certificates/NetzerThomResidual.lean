module

public import ThomGame.Certificates.NetzerThomResidualArithmetic

/-!
# Kernel-checked integer residual and coefficient partitions

The numerator uses the Gram denominator `121^2 * 10^12`. Each Gram entry
and each term of `Delta^2 - (561/2000) Delta` occurs exactly once. The
short-word proof relating a class's words is a separate certificate; this
file asserts no representation-theoretic consequence without that proof.
-/

@[expose] public section
namespace ThomGame.Certificates.NetzerThom

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificateMerge : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
      if x ≤ y then x :: certificateMerge n xs (y :: ys)
      else y :: certificateMerge n (x :: xs) ys

theorem certificateMerge_perm (n : ℕ) (xs ys : List ℕ) :
    (certificateMerge n xs ys).Perm (xs ++ ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
      cases xs with
      | nil => simp [certificateMerge]
      | cons x xs =>
          cases ys with
          | nil => simp [certificateMerge]
          | cons y ys =>
              simp only [certificateMerge]
              split_ifs
              · exact (ih xs (y :: ys)).cons x
              · exact ((ih (x :: xs) ys).cons y).trans
                  (List.perm_middle.symm)

def certificateSort : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | n + 1, xs =>
      certificateMerge (xs.length + 1)
        (certificateSort n (xs.take (xs.length / 2)))
        (certificateSort n (xs.drop (xs.length / 2)))

theorem certificateSort_perm (n : ℕ) (xs : List ℕ) :
    (certificateSort n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
      exact (certificateMerge_perm _ _ _).trans (by
        simpa only [List.take_append_drop] using
          (ih (xs.take (xs.length / 2))).append (ih (xs.drop (xs.length / 2))))

theorem gramPairIndices_sorted :
    certificateSort 15 gramPairIndices = List.range (121 * 121) := by rfl

theorem targetIndices_sorted :
    certificateSort 8 targetIndices = List.range 182 := by rfl

theorem gramPairIndices_partition :
    gramPairIndices.Perm (List.range (121 * 121)) := by
  rw [← gramPairIndices_sorted]
  exact (certificateSort_perm 15 gramPairIndices).symm

theorem targetIndices_partition :
    targetIndices.Perm (List.range 182) := by
  rw [← targetIndices_sorted]
  exact (certificateSort_perm 8 targetIndices).symm

end ThomGame.Certificates.NetzerThom
