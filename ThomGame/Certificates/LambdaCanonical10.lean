module

public import ThomGame.Certificates.LambdaCanonical08

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_080_correct :
    (raw_080.map canonical).filter (fun r => !r.isEmpty) = clean_080 := by
  decide +kernel

theorem clean_081_correct :
    (raw_081.map canonical).filter (fun r => !r.isEmpty) = clean_081 := by
  decide +kernel

theorem clean_082_correct :
    (raw_082.map canonical).filter (fun r => !r.isEmpty) = clean_082 := by
  decide +kernel

theorem clean_083_correct :
    (raw_083.map canonical).filter (fun r => !r.isEmpty) = clean_083 := by
  decide +kernel

theorem clean_084_correct :
    (raw_084.map canonical).filter (fun r => !r.isEmpty) = clean_084 := by
  decide +kernel

theorem clean_085_correct :
    (raw_085.map canonical).filter (fun r => !r.isEmpty) = clean_085 := by
  decide +kernel

theorem clean_086_correct :
    (raw_086.map canonical).filter (fun r => !r.isEmpty) = clean_086 := by
  decide +kernel

theorem clean_087_correct :
    (raw_087.map canonical).filter (fun r => !r.isEmpty) = clean_087 := by
  decide +kernel


end ThomGame.Lambda.Certificate
