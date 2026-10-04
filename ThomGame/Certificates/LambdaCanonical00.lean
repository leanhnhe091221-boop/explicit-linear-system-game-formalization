module

public import ThomGame.Certificates.LambdaCleanData

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_000_correct :
    (raw_000.map canonical).filter (fun r => !r.isEmpty) = clean_000 := by
  decide +kernel

theorem clean_001_correct :
    (raw_001.map canonical).filter (fun r => !r.isEmpty) = clean_001 := by
  decide +kernel

theorem clean_002_correct :
    (raw_002.map canonical).filter (fun r => !r.isEmpty) = clean_002 := by
  decide +kernel

theorem clean_003_correct :
    (raw_003.map canonical).filter (fun r => !r.isEmpty) = clean_003 := by
  decide +kernel

theorem clean_004_correct :
    (raw_004.map canonical).filter (fun r => !r.isEmpty) = clean_004 := by
  decide +kernel

theorem clean_005_correct :
    (raw_005.map canonical).filter (fun r => !r.isEmpty) = clean_005 := by
  decide +kernel

theorem clean_006_correct :
    (raw_006.map canonical).filter (fun r => !r.isEmpty) = clean_006 := by
  decide +kernel

theorem clean_007_correct :
    (raw_007.map canonical).filter (fun r => !r.isEmpty) = clean_007 := by
  decide +kernel


end ThomGame.Lambda.Certificate
