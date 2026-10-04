module

public import ThomGame.Certificates.LambdaCanonical01

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_024_correct :
    (raw_024.map canonical).filter (fun r => !r.isEmpty) = clean_024 := by
  decide +kernel

theorem clean_025_correct :
    (raw_025.map canonical).filter (fun r => !r.isEmpty) = clean_025 := by
  decide +kernel

theorem clean_026_correct :
    (raw_026.map canonical).filter (fun r => !r.isEmpty) = clean_026 := by
  decide +kernel

theorem clean_027_correct :
    (raw_027.map canonical).filter (fun r => !r.isEmpty) = clean_027 := by
  decide +kernel

theorem clean_028_correct :
    (raw_028.map canonical).filter (fun r => !r.isEmpty) = clean_028 := by
  decide +kernel

theorem clean_029_correct :
    (raw_029.map canonical).filter (fun r => !r.isEmpty) = clean_029 := by
  decide +kernel

theorem clean_030_correct :
    (raw_030.map canonical).filter (fun r => !r.isEmpty) = clean_030 := by
  decide +kernel

theorem clean_031_correct :
    (raw_031.map canonical).filter (fun r => !r.isEmpty) = clean_031 := by
  decide +kernel


end ThomGame.Lambda.Certificate
