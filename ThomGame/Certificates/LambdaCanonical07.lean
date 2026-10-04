module

public import ThomGame.Certificates.LambdaCanonical05

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_056_correct :
    (raw_056.map canonical).filter (fun r => !r.isEmpty) = clean_056 := by
  decide +kernel

theorem clean_057_correct :
    (raw_057.map canonical).filter (fun r => !r.isEmpty) = clean_057 := by
  decide +kernel

theorem clean_058_correct :
    (raw_058.map canonical).filter (fun r => !r.isEmpty) = clean_058 := by
  decide +kernel

theorem clean_059_correct :
    (raw_059.map canonical).filter (fun r => !r.isEmpty) = clean_059 := by
  decide +kernel

theorem clean_060_correct :
    (raw_060.map canonical).filter (fun r => !r.isEmpty) = clean_060 := by
  decide +kernel

theorem clean_061_correct :
    (raw_061.map canonical).filter (fun r => !r.isEmpty) = clean_061 := by
  decide +kernel

theorem clean_062_correct :
    (raw_062.map canonical).filter (fun r => !r.isEmpty) = clean_062 := by
  decide +kernel

theorem clean_063_correct :
    (raw_063.map canonical).filter (fun r => !r.isEmpty) = clean_063 := by
  decide +kernel


end ThomGame.Lambda.Certificate
