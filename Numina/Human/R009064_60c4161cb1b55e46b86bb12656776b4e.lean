import Mathlib

/- What is the value of (2 * a^-1 + a^-1 / 2) / a when a = 1/2 ?
(A) 1
(B) 2
(C) 5/2
(D) 10
(E) 20
 -/
theorem algebra_97202 {a : ℝ} (ha : a ≠ 0) (ha' : a = 1 / 2) : (2 / a + 1 / (2 * a)) / a = 10 := by
  -- plug in the value 1/2 into the exrpession then calculate
  rw [ha']
  calc
    ((2:ℝ) / (1 / 2) + 1 / (2 * (1 / 2))) / (1 / 2) = (4 + 1) / (1/2) := by norm_num
    _ = 5 * 2 := by norm_num
    _ = 10 := by norm_num