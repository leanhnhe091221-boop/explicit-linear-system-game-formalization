module

public import ThomGame.Certificates.LambdaCleanData

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_008_correct :
    (raw_008.map canonical).filter (fun r => !r.isEmpty) = clean_008 := by
  decide +kernel

theorem clean_009_correct :
    (raw_009.map canonical).filter (fun r => !r.isEmpty) = clean_009 := by
  decide +kernel

theorem clean_010_correct :
    (raw_010.map canonical).filter (fun r => !r.isEmpty) = clean_010 := by
  decide +kernel

theorem clean_011_correct :
    (raw_011.map canonical).filter (fun r => !r.isEmpty) = clean_011 := by
  decide +kernel

theorem clean_012_correct :
    (raw_012.map canonical).filter (fun r => !r.isEmpty) = clean_012 := by
  decide +kernel

theorem clean_013_correct :
    (raw_013.map canonical).filter (fun r => !r.isEmpty) = clean_013 := by
  decide +kernel

theorem clean_014_correct :
    (raw_014.map canonical).filter (fun r => !r.isEmpty) = clean_014 := by
  decide +kernel

theorem clean_015_correct :
    (raw_015.map canonical).filter (fun r => !r.isEmpty) = clean_015 := by
  decide +kernel


end ThomGame.Lambda.Certificate
