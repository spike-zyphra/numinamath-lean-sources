import Mathlib

theorem algebra_310522 (x y : ℝ) (A B : ℝ × ℝ)
    (hA : A.1 = x - (3 - Real.sqrt 5) / 2 * y ∧ A.2 = 1)
    (hB : B.1 = x - (3 + Real.sqrt 5) / 2 * y ∧ B.2 = -1)
    (hAB : A.1 * B.1 + A.2 * B.2 = 0) :
    x ^ 2 - x * y + y ^ 2 - 1 ≥ -2 / 5 := by

  rcases hA with ⟨hx_A, hy_A⟩
  rcases hB with ⟨hx_B, hy_B⟩
  have eq1 : (x - (3 - Real.sqrt 5) / 2 * y) * (x - (3 + Real.sqrt 5) / 2 * y) + (1 : ℝ) * (-1) = 0 := by
    rw [hx_A, hy_A, hx_B, hy_B] at hAB
    linarith

  have h1 : x ^ 2 - 3 * x * y + y ^ 2 = 1 := by 
    nlinarith [eq1, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]

  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 1 / Real.sqrt 5), sq_nonneg (y - (-1 / Real.sqrt 5)), sq_nonneg (x + 1 / Real.sqrt 5), sq_nonneg (y + 1 / Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0)]