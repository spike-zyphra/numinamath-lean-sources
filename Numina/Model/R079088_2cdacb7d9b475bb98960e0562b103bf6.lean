import Mathlib

theorem algebra_157289 {A B : ℝ}
    (hA : A = 10^9 - 987654321) (hB : B = (123456789 + 1) / 10) :
    Real.sqrt (A * B) = 12345679 := by
  have hA' : A = (12345679 : ℝ) := by
    rw [hA]
    norm_num
  have hB' : B = (12345679 : ℝ) := by
    rw [hB]
    norm_num
  rw [hA', hB']
  rw [show Real.sqrt ((12345679 : ℝ) * (12345679 : ℝ)) = Real.sqrt ((12345679 : ℝ) ^ 2) by ring_nf]
  rw [Real.sqrt_sq (by norm_num)]
  all_goals norm_num