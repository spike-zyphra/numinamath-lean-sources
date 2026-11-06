import Mathlib

theorem algebra_794 : Real.sqrt ((4417^3 - 3000^3) / 109 + 13 * 13251000) = 7417 * Real.sqrt 13 := by
  have h2 : ((4417^3 - 3000^3) / 109 + 13 * 13251000 : ℝ) = (13 * (7417 : ℝ) ^ 2) := by
    norm_num
  rw [h2]
  have h3 : Real.sqrt (13 * (7417 : ℝ) ^ 2) = (7417 * Real.sqrt 13) := by
    have h4 : Real.sqrt (13 * (7417 : ℝ) ^ 2) = Real.sqrt (13 : ℝ) * Real.sqrt (7417^2 : ℝ) := by
      have h7 : (13 * (7417 : ℝ) ^ 2) = (13 : ℝ) * (7417^2 : ℝ) := by ring
      rw [h7]
      have h8 : Real.sqrt ((13 : ℝ) * (7417^2 : ℝ)) = Real.sqrt (13 : ℝ) * Real.sqrt (7417^2 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
      linarith [h8]
    have h9 : Real.sqrt ((7417 : ℝ) ^ 2) = (7417 : ℝ) := by
      have h10 : (7417 : ℝ) ≥ 0 := by norm_num
      exact Real.sqrt_sq h10
    rw [h4, h9]
    all_goals ring_nf <;> norm_num
  exact h3