module

public import ThomGame.Certificates.LambdaCanonical11

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_104_correct :
    (raw_104.map canonical).filter (fun r => !r.isEmpty) = clean_104 := by
  decide +kernel

theorem clean_105_correct :
    (raw_105.map canonical).filter (fun r => !r.isEmpty) = clean_105 := by
  decide +kernel

theorem clean_106_correct :
    (raw_106.map canonical).filter (fun r => !r.isEmpty) = clean_106 := by
  decide +kernel

theorem clean_107_correct :
    (raw_107.map canonical).filter (fun r => !r.isEmpty) = clean_107 := by
  decide +kernel

theorem clean_108_correct :
    (raw_108.map canonical).filter (fun r => !r.isEmpty) = clean_108 := by
  decide +kernel

theorem clean_109_correct :
    (raw_109.map canonical).filter (fun r => !r.isEmpty) = clean_109 := by
  decide +kernel

theorem clean_110_correct :
    (raw_110.map canonical).filter (fun r => !r.isEmpty) = clean_110 := by
  decide +kernel

theorem clean_111_correct :
    (raw_111.map canonical).filter (fun r => !r.isEmpty) = clean_111 := by
  decide +kernel


end ThomGame.Lambda.Certificate
