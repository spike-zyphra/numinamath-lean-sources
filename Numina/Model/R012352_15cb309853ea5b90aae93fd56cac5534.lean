import Mathlib

theorem algebra_598413 {a b : ℝ} (ha : a ^ 2 ≤ 1) (hb : b ^ 2 ≤ 1)
    (h : a * Real.sqrt (1 - b ^ 2) + b * Real.sqrt (1 - a ^ 2) = 1) :
    a ^ 2 + b ^ 2 = 1 := by
  have h1 : 0 ≤ Real.sqrt (1 - b ^ 2) := Real.sqrt_nonneg (1 - b ^ 2)
  have h2 : 0 ≤ Real.sqrt (1 - a ^ 2) := Real.sqrt_nonneg (1 - a ^ 2)
  have h3 : Real.sqrt (1 - b ^ 2) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have h4 : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have eq1 : (a * Real.sqrt (1 - b ^ 2) + b * Real.sqrt (1 - a ^ 2)) ^ 2 = 1 := by
    rw [h]
    norm_num
  have eq2 : (a * Real.sqrt (1 - b ^ 2) + b * Real.sqrt (1 - a ^ 2)) ^ 2
      = a^2 * (1 - b^2) + b^2 * (1 - a^2) + 2 * (a * b * (Real.sqrt (1 - b^2) * Real.sqrt (1 - a^2))) := by
    calc
      (a * Real.sqrt (1 - b ^ 2) + b * Real.sqrt (1 - a ^ 2)) ^ 2
          = (a * Real.sqrt (1 - b^2)) ^ 2 + (b * Real.sqrt (1 - a^2)) ^ 2 + 2 * (a * Real.sqrt (1 - b^2) * (b * Real.sqrt (1 - a^2))) := by ring
      _ = a^2 * (Real.sqrt (1 - b^2) ^2) + b^2 * (Real.sqrt (1 - a^2) ^2) + 2 * (a * b * (Real.sqrt (1 - b^2) * Real.sqrt (1 - a^2))) := by ring
      _ = a^2 * (1 - b ^ 2) + b^2 * (1 - a ^ 2) + 2 * (a * b * (Real.sqrt (1 - b^2) * Real.sqrt (1 - a^2))) := by 
        rw [h3, h4]
  rw [eq2] at eq1
  nlinarith [sq_nonneg (a - Real.sqrt (1 - b ^ 2)), sq_nonneg (b - Real.sqrt (1 - a ^ 2)), 
          sq_nonneg (a + b), sq_nonneg (Real.sqrt (1 - b ^ 2) - Real.sqrt (1 - a ^ 2)), 
          Real.sqrt_nonneg (1 - b ^ 2), Real.sqrt_nonneg (1 - a ^ 2), 
          sq_nonneg (a * Real.sqrt (1 - b ^ 2) - b * Real.sqrt (1 - a ^ 2)), 
          mul_nonneg (Real.sqrt_nonneg (1 - b ^ 2)) (Real.sqrt_nonneg (1 - a ^ 2)), 
          h3, h4, sq_nonneg (a^2 - b^2), sq_nonneg (a - b)
]