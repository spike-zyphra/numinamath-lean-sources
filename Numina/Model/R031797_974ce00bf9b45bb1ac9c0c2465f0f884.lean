import Mathlib

open Real

theorem inequalities_3169 :
  IsGreatest {K | ∀ x y : ℝ, 0 < x → 0 < y → x + y = 1 → (x ^ 2 + y + 1) * (y ^ 2 + x + 1) ≥ K * x ^ 2 * y ^ 2} 49 := by
  constructor
  · -- Show 49 is in the set
    intro x y hx hy h'
    have h1 : y = 1 - x := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x) - 1 / 2), sq_nonneg (x ^ 2 - (1 - x) ^ 2),
      sq_nonneg (x - (1 - x)), sq_nonneg (x * (1 - x) - 1 / 4), mul_pos hx (show (0 : ℝ) < 1 - x by nlinarith)]
  · -- Show 49 is the greatest
    intro K h
    have h1 : ∀ x y : ℝ, 0 < x → 0 < y → x + y = 1 → (x ^ 2 + y + 1) * (y ^ 2 + x + 1) ≥ K * x ^ 2 * y ^ 2 := h
    have h2 := h1 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    nlinarith