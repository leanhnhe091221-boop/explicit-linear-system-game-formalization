module

public import ThomGame.Certificates.LambdaCanonical04

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_048_correct :
    (raw_048.map canonical).filter (fun r => !r.isEmpty) = clean_048 := by
  decide +kernel

theorem clean_049_correct :
    (raw_049.map canonical).filter (fun r => !r.isEmpty) = clean_049 := by
  decide +kernel

theorem clean_050_correct :
    (raw_050.map canonical).filter (fun r => !r.isEmpty) = clean_050 := by
  decide +kernel

theorem clean_051_correct :
    (raw_051.map canonical).filter (fun r => !r.isEmpty) = clean_051 := by
  decide +kernel

theorem clean_052_correct :
    (raw_052.map canonical).filter (fun r => !r.isEmpty) = clean_052 := by
  decide +kernel

theorem clean_053_correct :
    (raw_053.map canonical).filter (fun r => !r.isEmpty) = clean_053 := by
  decide +kernel

theorem clean_054_correct :
    (raw_054.map canonical).filter (fun r => !r.isEmpty) = clean_054 := by
  decide +kernel

theorem clean_055_correct :
    (raw_055.map canonical).filter (fun r => !r.isEmpty) = clean_055 := by
  decide +kernel


end ThomGame.Lambda.Certificate
