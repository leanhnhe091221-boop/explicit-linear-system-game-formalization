module

public import ThomGame.Certificates.LambdaCanonical10

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_096_correct :
    (raw_096.map canonical).filter (fun r => !r.isEmpty) = clean_096 := by
  decide +kernel

theorem clean_097_correct :
    (raw_097.map canonical).filter (fun r => !r.isEmpty) = clean_097 := by
  decide +kernel

theorem clean_098_correct :
    (raw_098.map canonical).filter (fun r => !r.isEmpty) = clean_098 := by
  decide +kernel

theorem clean_099_correct :
    (raw_099.map canonical).filter (fun r => !r.isEmpty) = clean_099 := by
  decide +kernel

theorem clean_100_correct :
    (raw_100.map canonical).filter (fun r => !r.isEmpty) = clean_100 := by
  decide +kernel

theorem clean_101_correct :
    (raw_101.map canonical).filter (fun r => !r.isEmpty) = clean_101 := by
  decide +kernel

theorem clean_102_correct :
    (raw_102.map canonical).filter (fun r => !r.isEmpty) = clean_102 := by
  decide +kernel

theorem clean_103_correct :
    (raw_103.map canonical).filter (fun r => !r.isEmpty) = clean_103 := by
  decide +kernel


end ThomGame.Lambda.Certificate
