import Mathlib

theorem calculus_12496 (a b : ℝ × ℝ)
    (ha : Real.sqrt (a.1^2 + a.2^2) = 3) (hb : Real.sqrt (b.1^2 + b.2^2) = 6) :
    (a.1 + b.1) * (a.1 - b.1) + (a.2 + b.2) * (a.2 - b.2) = -27 := by
  have ha2 : a.1^2 + a.2^2 = 9 := by
    calc
      a.1^2 + a.2^2 = (Real.sqrt (a.1^2 + a.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 3^2 := by rw [ha]
      _ = 9 := by norm_num
  have hb2 : b.1^2 + b.2^2 = 36 := by
    calc
      b.1^2 + b.2^2 = (Real.sqrt (b.1^2 + b.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 6^2 := by rw [hb]
      _ = 36 := by norm_num
  calc
    (a.1 + b.1) * (a.1 - b.1) + (a.2 + b.2) * (a.2 - b.2)
      = (a.1^2 - b.1^2) + (a.2^2 - b.2^2) := by ring
    _ = (a.1^2 + a.2^2) - (b.1^2 + b.2^2) := by ring
    _ = 9 - 36 := by rw [ha2, hb2]
    _ = -27 := by norm_num