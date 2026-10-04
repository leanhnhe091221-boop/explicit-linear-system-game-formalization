module

public import ThomGame.Certificates.LambdaCanonical06

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_064_correct :
    (raw_064.map canonical).filter (fun r => !r.isEmpty) = clean_064 := by
  decide +kernel

theorem clean_065_correct :
    (raw_065.map canonical).filter (fun r => !r.isEmpty) = clean_065 := by
  decide +kernel

theorem clean_066_correct :
    (raw_066.map canonical).filter (fun r => !r.isEmpty) = clean_066 := by
  decide +kernel

theorem clean_067_correct :
    (raw_067.map canonical).filter (fun r => !r.isEmpty) = clean_067 := by
  decide +kernel

theorem clean_068_correct :
    (raw_068.map canonical).filter (fun r => !r.isEmpty) = clean_068 := by
  decide +kernel

theorem clean_069_correct :
    (raw_069.map canonical).filter (fun r => !r.isEmpty) = clean_069 := by
  decide +kernel

theorem clean_070_correct :
    (raw_070.map canonical).filter (fun r => !r.isEmpty) = clean_070 := by
  decide +kernel

theorem clean_071_correct :
    (raw_071.map canonical).filter (fun r => !r.isEmpty) = clean_071 := by
  decide +kernel


end ThomGame.Lambda.Certificate
