import Mathlib

theorem algebra_102580 {a : ℝ} (ha : a > 0) (f : ℝ → ℝ) (hf : f = fun x => x^2 + x + a)
    (m : ℝ) (hm : f m < 0) : f (m + 1) > 0 := by
  have h1 : f m = m ^ 2 + m + a := by
    rw [hf]
  have h2 : f (m + 1) = (m + 1) ^ 2 + (m + 1) + a := by
    rw [hf]
  rw [h1] at hm
  rw [h2]
  nlinarith [sq_nonneg (m + 1), sq_nonneg (m + 0.5), sq_nonneg (m - 0.5), sq_pos_of_pos ha]