import Mathlib

theorem algebra_316090 {a b : ℝ} (ha : a = 16 + 16 / 15) (hb : b = 16) :
    Real.log a = Real.log b + Real.log (b / (b - 1)) := by
  rw [ha, hb]
  have h1 : Real.log (16 + (16 / 15 : ℝ)) = Real.log (256 / 15) := by
    norm_num
  have h2 : Real.log (16 : ℝ) + Real.log ((16 : ℝ) / (16 - 1 : ℝ)) = Real.log (16 : ℝ) + (Real.log (16 : ℝ) - Real.log (15 : ℝ)) := by
    have h3 : Real.log ((16 : ℝ) / (16 - 1 : ℝ)) = Real.log (16 : ℝ) - Real.log (15 : ℝ) := by
      rw [show (16 : ℝ) / (16 - 1 : ℝ) = (16 : ℝ) / (15 : ℝ) by norm_num]
      rw [Real.log_div (by norm_num) (by norm_num)]
    rw [h3]
  have h4 : Real.log (256 / 15 : ℝ) = Real.log (256 : ℝ) - Real.log (15 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h5 : Real.log (256 : ℝ) = 2 * Real.log (16 : ℝ) := by
    have h6 : (256 : ℝ) = (16 : ℝ) ^ 2 := by norm_num
    rw [h6]
    have h7 : Real.log ((16 : ℝ) ^ 2) = 2 * Real.log (16 : ℝ) := by
      simp [Real.log_pow]
      <;> ring
    linarith [h7]

  rw [h1, h4, h2]
  linarith [h5]