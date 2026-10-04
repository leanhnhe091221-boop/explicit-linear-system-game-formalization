module

public import ThomGame.Certificates.LambdaCanonical02

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_032_correct :
    (raw_032.map canonical).filter (fun r => !r.isEmpty) = clean_032 := by
  decide +kernel

theorem clean_033_correct :
    (raw_033.map canonical).filter (fun r => !r.isEmpty) = clean_033 := by
  decide +kernel

theorem clean_034_correct :
    (raw_034.map canonical).filter (fun r => !r.isEmpty) = clean_034 := by
  decide +kernel

theorem clean_035_correct :
    (raw_035.map canonical).filter (fun r => !r.isEmpty) = clean_035 := by
  decide +kernel

theorem clean_036_correct :
    (raw_036.map canonical).filter (fun r => !r.isEmpty) = clean_036 := by
  decide +kernel

theorem clean_037_correct :
    (raw_037.map canonical).filter (fun r => !r.isEmpty) = clean_037 := by
  decide +kernel

theorem clean_038_correct :
    (raw_038.map canonical).filter (fun r => !r.isEmpty) = clean_038 := by
  decide +kernel

theorem clean_039_correct :
    (raw_039.map canonical).filter (fun r => !r.isEmpty) = clean_039 := by
  decide +kernel


end ThomGame.Lambda.Certificate
