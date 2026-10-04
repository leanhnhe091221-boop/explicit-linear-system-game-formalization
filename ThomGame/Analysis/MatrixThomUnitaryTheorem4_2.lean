module

public import ThomGame.Analysis.MatrixThomTheorem4_2
public import ThomGame.Analysis.MatrixInternalUnitaryLifting
public import ThomGame.Analysis.UnitaryAlgebraTransport

/-!
# Thom Theorem 4.2 for given quotient unitaries

The anchor itself implies commutation with the internal common algebra.
Exact commuting representatives are constructed using the proved
internal unitary lifting theorem, then the matrix theorem applies.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem matrixThom_theorem_4_2_of_unitaries {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)))
    (hDA : ∀ n, D n ≤ A n) (L : Filter ι) {h : Nat}
    (u : Fin h → unitary (MatrixTracialQuotient dims L))
    (hincl : ∀ j, (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L) (u j)).symm.toStarAlgHom ≤
      matrixInternalQuotient dims A L)
    (hanchor : matrixInternalQuotient dims A L ⊓
      StarSubalgebra.centralizer ℂ (Set.range (fun j => (u j).val)) = matrixInternalQuotient dims D L) :
    ∀ j, (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L) (u j)).symm.toStarAlgHom =
      matrixInternalQuotient dims A L := by
  have hcomm (x : MatrixTracialQuotient dims L) (hx : x ∈ matrixInternalQuotient dims D L) :
      ∀ j, Commute (u j).val x := by
    have hx' : x ∈ matrixInternalQuotient dims A L ⊓
        StarSubalgebra.centralizer ℂ (Set.range (fun j => (u j).val)) := by rwa [hanchor]
    exact (unitaryRangeCommutant_mem_iff u x).mp hx'.2
  have hu j : (u j).val ∈ StarSubalgebra.centralizer ℂ
      (matrixInternalQuotient dims D L : Set (MatrixTracialQuotient dims L)) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro x hx
    exact ⟨(hcomm x hx j).eq.symm,
      (hcomm (star x) ((matrixInternalQuotient dims D L).star_mem' hx) j).eq.symm⟩
  choose V hV hv using fun j => exists_matrixInternalCommutant_unitary_lift dims D
    (fun n => NeZero.pos (dims n)) L (u j) (hu j)
  let U := fun n j => V j n
  have hunit j : unitarySequenceToAlgebra dims L (fun n => U n j) = u j := Subtype.ext (hv j)
  have hclass : matrixTupleClass dims U L = fun j => (u j).val := funext hv
  have hanchor' : matrixInternalQuotient dims A L ⊓ matrixRelativeCommutant dims U L =
      matrixInternalQuotient dims D L := by
    simpa only [matrixRelativeCommutant, hclass] using hanchor
  have hi j : (matrixInternalQuotient dims A L).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims L)
        (unitarySequenceToAlgebra dims L (fun n => U n j))).symm.toStarAlgHom ≤
      matrixInternalQuotient dims A L := by
    rw [hunit]
    exact hincl j
  have he := matrixThom_theorem_4_2 dims A D hDA U
    (fun n j x hx => (hV j n x hx).symm) L hi hanchor'
  intro j
  simpa only [hunit] using he j

end ThomGame.Analysis
