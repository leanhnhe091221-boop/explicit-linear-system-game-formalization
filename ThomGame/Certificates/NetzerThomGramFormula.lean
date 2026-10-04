module

public import ThomGame.Certificates.NetzerThomNumericBounds
public import Mathlib.Data.List.GetD

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
open scoped BigOperators

theorem gramEntry_eq_coefficient {i j : ℕ} (hi : i < 121) (hj : j < 121) :
    gramEntry i j = gramCoefficient i j := by
  unfold gramEntry
  rw [← gramTable_checked]
  rw [List.getD_eq_getElem ((List.range 121).map gramRow) [] (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  unfold gramRow
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem dot_eq_sum_fin {n : ℕ} (as bs : List ℤ)
    (ha : as.length = n) (hb : bs.length = n) :
    dot as bs = ∑ k : Fin n, as.getD k 0 * bs.getD k 0 := by
  induction n generalizing as bs with
  | zero =>
      have hea : as = [] := List.length_eq_zero_iff.mp ha
      have heb : bs = [] := List.length_eq_zero_iff.mp hb
      subst as; subst bs
      simp [dot]
  | succ n ih =>
      cases as with
      | nil => simp at ha
      | cons a as =>
          cases bs with
          | nil => simp at hb
          | cons b bs =>
              have ha' : as.length = n := by simpa using ha
              have hb' : bs.length = n := by simpa using hb
              rw [Fin.sum_univ_succ]
              simp only [dot, Fin.val_zero, List.getD_cons_zero,
                Fin.val_succ, List.getD_cons_succ, ih as bs ha' hb']

theorem rootColumn_length {i : ℕ} (hi : i < 121) :
    (rootColumns.getD i []).length = 112 := by
  have hil : i < rootColumns.length := by simpa only [rootColumns_shape.1] using hi
  rw [List.getD_eq_getElem _ _ hil]
  have h := (List.all_eq_true.mp rootColumns_shape.2) _ (List.getElem_mem hil)
  exact of_decide_eq_true h

def rootCoefficient (i : Fin 121) (k : Fin 112) : ℤ :=
  (rootColumns.getD i []).getD k 0

theorem gramEntry_formula (i j : Fin 121) :
    gramEntry i j = ∑ k : Fin 112, rootCoefficient i k * rootCoefficient j k := by
  rw [gramEntry_eq_coefficient i.isLt j.isLt]
  exact dot_eq_sum_fin _ _ (rootColumn_length i.isLt) (rootColumn_length j.isLt)

end ThomGame.Certificates.NetzerThom
