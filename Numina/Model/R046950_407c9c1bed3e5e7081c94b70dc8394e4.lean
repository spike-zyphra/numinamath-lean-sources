import Mathlib

open Real

theorem inequalities_246973 (x : ℝ) (hx : x ≥ 1 / 2) :
    ∃ n : ℤ, |x ^ 2 - n| ≤ sqrt (x - 1 / 4) := by
  use round (x ^ 2)
  have h5 : |x ^ 2 - (↑(round (x ^ 2)) : ℝ)| ≤ (1 / 2 : ℝ) := by 
    apply abs_sub_round
  have h7 : sqrt (x - 1 / 4) ≥ (1 / 2 : ℝ) := by
    have h8 : (x - 1 / 4 : ℝ) ≥ (1 / 4 : ℝ) := by
      linarith
    have h9 : sqrt (x - 1 / 4) ≥ sqrt (1 / 4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h10 : sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h10]
  linarith [abs_le.mp (show |x ^ 2 - (↑(round (x ^ 2)) : ℝ)| ≤ (1 / 2 : ℝ) by simpa using h5)]