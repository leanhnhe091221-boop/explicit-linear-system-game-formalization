module

public import ThomGame.Certificates.LambdaCanonical12

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_112_correct :
    (raw_112.map canonical).filter (fun r => !r.isEmpty) = clean_112 := by
  decide +kernel

theorem clean_113_correct :
    (raw_113.map canonical).filter (fun r => !r.isEmpty) = clean_113 := by
  decide +kernel

theorem clean_114_correct :
    (raw_114.map canonical).filter (fun r => !r.isEmpty) = clean_114 := by
  decide +kernel

theorem clean_115_correct :
    (raw_115.map canonical).filter (fun r => !r.isEmpty) = clean_115 := by
  decide +kernel

theorem clean_116_correct :
    (raw_116.map canonical).filter (fun r => !r.isEmpty) = clean_116 := by
  decide +kernel

theorem clean_117_correct :
    (raw_117.map canonical).filter (fun r => !r.isEmpty) = clean_117 := by
  decide +kernel

theorem clean_118_correct :
    (raw_118.map canonical).filter (fun r => !r.isEmpty) = clean_118 := by
  decide +kernel

theorem clean_119_correct :
    (raw_119.map canonical).filter (fun r => !r.isEmpty) = clean_119 := by
  decide +kernel


end ThomGame.Lambda.Certificate
