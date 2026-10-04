module

public import ThomGame.Certificates.NetzerThomNumericBounds

@[expose] public section
namespace ThomGame.Certificates.NetzerThom
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gramClassMass_bound :
    (residualClasses.flatMap (fun c => c.pairs.map (fun ij => (gramEntry ij.1 ij.2).natAbs))).sum ≤
      20000 * 14641000000000000 := by decide +kernel

theorem targetClassMass_bound :
    (residualClasses.flatMap (fun c => c.terms.map (fun i => (targetTerms.getD i ([],0)).2.natAbs))).sum ≤
      600 * 14641000000000000 := by decide +kernel

end ThomGame.Certificates.NetzerThom
