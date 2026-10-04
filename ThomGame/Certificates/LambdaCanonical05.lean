module

public import ThomGame.Certificates.LambdaCanonical03

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_040_correct :
    (raw_040.map canonical).filter (fun r => !r.isEmpty) = clean_040 := by
  decide +kernel

theorem clean_041_correct :
    (raw_041.map canonical).filter (fun r => !r.isEmpty) = clean_041 := by
  decide +kernel

theorem clean_042_correct :
    (raw_042.map canonical).filter (fun r => !r.isEmpty) = clean_042 := by
  decide +kernel

theorem clean_043_correct :
    (raw_043.map canonical).filter (fun r => !r.isEmpty) = clean_043 := by
  decide +kernel

theorem clean_044_correct :
    (raw_044.map canonical).filter (fun r => !r.isEmpty) = clean_044 := by
  decide +kernel

theorem clean_045_correct :
    (raw_045.map canonical).filter (fun r => !r.isEmpty) = clean_045 := by
  decide +kernel

theorem clean_046_correct :
    (raw_046.map canonical).filter (fun r => !r.isEmpty) = clean_046 := by
  decide +kernel

theorem clean_047_correct :
    (raw_047.map canonical).filter (fun r => !r.isEmpty) = clean_047 := by
  decide +kernel


end ThomGame.Lambda.Certificate
