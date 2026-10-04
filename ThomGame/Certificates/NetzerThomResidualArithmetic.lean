module

public import ThomGame.Certificates.NetzerThomResidualData

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

theorem residualMass_exact : residualMass = 328114781270964 := by rfl

theorem residualMass_bound :
    400 * residualMass ≤ 9 * 14641000000000000 := by
  rw [residualMass_exact]
  norm_num

theorem residual_augmentation :
    (residualClasses.map residualNumerator).sum = 0 := by rfl

end ThomGame.Certificates.NetzerThom
