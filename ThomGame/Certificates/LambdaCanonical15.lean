module

public import ThomGame.Certificates.LambdaCanonical13

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_120_correct :
    (raw_120.map canonical).filter (fun r => !r.isEmpty) = clean_120 := by
  decide +kernel

theorem clean_121_correct :
    (raw_121.map canonical).filter (fun r => !r.isEmpty) = clean_121 := by
  decide +kernel


end ThomGame.Lambda.Certificate
