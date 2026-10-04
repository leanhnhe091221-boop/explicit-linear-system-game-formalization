module

public import ThomGame.Certificates.LambdaCanonical07

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_072_correct :
    (raw_072.map canonical).filter (fun r => !r.isEmpty) = clean_072 := by
  decide +kernel

theorem clean_073_correct :
    (raw_073.map canonical).filter (fun r => !r.isEmpty) = clean_073 := by
  decide +kernel

theorem clean_074_correct :
    (raw_074.map canonical).filter (fun r => !r.isEmpty) = clean_074 := by
  decide +kernel

theorem clean_075_correct :
    (raw_075.map canonical).filter (fun r => !r.isEmpty) = clean_075 := by
  decide +kernel

theorem clean_076_correct :
    (raw_076.map canonical).filter (fun r => !r.isEmpty) = clean_076 := by
  decide +kernel

theorem clean_077_correct :
    (raw_077.map canonical).filter (fun r => !r.isEmpty) = clean_077 := by
  decide +kernel

theorem clean_078_correct :
    (raw_078.map canonical).filter (fun r => !r.isEmpty) = clean_078 := by
  decide +kernel

theorem clean_079_correct :
    (raw_079.map canonical).filter (fun r => !r.isEmpty) = clean_079 := by
  decide +kernel


end ThomGame.Lambda.Certificate
