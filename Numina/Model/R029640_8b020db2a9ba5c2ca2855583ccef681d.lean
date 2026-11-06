import Mathlib

theorem algebra_318939 (x : ℝ) (hx : x^2 + x - 2 ≠ 0 ∧ x^2 + 7 * x + 10 ≠ 0) :
    1 / (x^2 + x - 2) + 1 / (x^2 + 7 * x + 10) = 2 ↔ x = -2 + Real.sqrt 10 ∨ x = -2 - Real.sqrt 10 := by
  constructor
  · -- Assume $\frac{1}{x^{2}+x-2}+\frac{1}{x^{2}+7x+10}=2$ (Necessary step)
    intro h
    have h1 : x^2 + x - 2 ≠ 0 := hx.1
    have h2 : x^2 + 7 * x + 10 ≠ 0 := hx.2
    field_simp [h1, h2] at h
    have h3 : (x + 2) * (x ^ 2 + 4 * x - 6) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (x ^ 2 + x - 2 : ℝ) ≠ 0 by exact h1), sq_pos_of_ne_zero (show (x ^ 2 + 7 * x + 10 : ℝ) ≠ 0 by exact h2)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case $x + 2 = 0$, which implies $x = -2$, an invalid solution
      have h6 : x = -2 := by linarith
      have h7 : x ^ 2 + x - 2 = 0 := by
        rw [h6]
        norm_num
      contradiction
    · -- Case $x^2 + 4 x - 6 = 0$
      have h8 : x^2 + 4 * x - 6 = 0 := by
        linarith
      have h9 : (x - (-2 + Real.sqrt 10)) * (x - (-2 - Real.sqrt 10)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (10 : ℝ) > 0 by norm_num : (10 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- Solving  x - (-2 + sqrt 10) =0
        left
        linarith
      · -- Solving x - (-2 - sqrt 10) =0
        right
        linarith
  · -- Assume $x = -2 + \sqrt{10}$ or $x = -2 - \sqrt{10}$ (Sufficient step)
    rintro (h | h)
    · -- When x = -2 + sqrt 10
      rw [h]
      have h1 : (-2 + Real.sqrt 10 : ℝ) ^ 2 + (-2 + Real.sqrt 10) - 2 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
      have h2 : (-2 + Real.sqrt 10 : ℝ) ^ 2 + 7 * (-2 + Real.sqrt 10) + 10 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
    · -- When x = -2 - sqrt 10
      rw [h]
      have h1 : (-2 - Real.sqrt 10 : ℝ) ^ 2 + (-2 - Real.sqrt 10) - 2 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
      have h2 : (-2 - Real.sqrt 10 : ℝ) ^ 2 + 7 * (-2 - Real.sqrt 10) + 10 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (0 : ℝ) ≤ 10)]