module

public import ThomGame.Certificates.NetzerThomResidualArithmetic

/-! Additional finite shape and coefficient bounds, checked by kernel reduction. -/

@[expose] public section
namespace ThomGame.Certificates.NetzerThom

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gramMass : ℕ := ((gramTable.flatten).map Int.natAbs).sum

theorem gramMass_bound : gramMass ≤ 20000 * 14641000000000000 := by decide +kernel

theorem targetMass_bound :
    (targetTerms.map (fun e => e.2.natAbs)).sum ≤ 600 * 14641000000000000 := by
  decide +kernel

theorem basisWords_shape : basisWords.length = 121 ∧
    basisWords.all (fun w => decide (w.length ≤ 2) && w.all (fun a => decide (a < 12))) = true := by
  decide +kernel

theorem targetTerms_length : targetTerms.length = 182 := by rfl

theorem residualClasses_shape :
    residualClasses.all (fun c =>
      decide (c.representative.length ≤ 4) &&
      c.representative.all (fun a => decide (a < 12)) &&
      c.pairs.all (fun ij => decide (ij.1 < 121 ∧ ij.2 < 121)) &&
      c.terms.all (fun i => decide (i < 182))) = true := by rfl

def laplacianTerms : List (List ℕ × ℤ) :=
  ([],12) :: (List.range 12).map (fun i => ([i],-1))

theorem targetTerms_formula : targetTerms =
    (laplacianTerms.flatMap fun a => laplacianTerms.map fun b =>
      (a.1 ++ b.1, a.2 * b.2 * 14641000000000000)) ++
    laplacianTerms.map (fun a => (a.1, -a.2 * 561 * 7320500000000)) := by rfl

end ThomGame.Certificates.NetzerThom
