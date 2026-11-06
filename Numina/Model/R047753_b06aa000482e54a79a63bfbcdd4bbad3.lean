import Mathlib

theorem algebra_611195 (x : ℝ) (h₀ : 0 < x) (h₁ : Real.cos (Real.arctan x) = x) : x ^ 2 = (-1 + Real.sqrt 5) / 2 := by
  have h2 : Real.cos (Real.arctan x) = 1 / Real.sqrt (1 + x^2) := by
    rw [Real.cos_arctan]
    <;> field_simp
  rw [h2] at h₁
  have h3 : 1 / Real.sqrt (1 + x^2) = x := by linarith
  have h4 : 0 < Real.sqrt (1 + x^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have h8 : x * Real.sqrt (1 + x^2) = 1 := by
    have h9 : Real.sqrt (1 + x^2) ≠ 0 := by
      linarith [Real.sqrt_nonneg (1 + x^2), h4]
    field_simp [h9] at h3
    nlinarith
  have h9 : (x) ^ 2 * (1 + x ^ 2) = 1 := by
    calc
      x ^ 2 * (1 + x ^ 2) = (x * Real.sqrt (1 + x^2)) ^ 2 := by
        have h11 : (Real.sqrt (1 + x^2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by nlinarith)
        nlinarith [h11]
      _ = 1 ^ 2 := by
        rw [show x * Real.sqrt (1 + x^2) = 1 by nlinarith [h8]]
      _ = 1 := by norm_num
  have h10 : (x ^ 2) ^ 2 + x ^ 2 - 1 = 0 := by
    nlinarith [h9]
  have h11 : x ^ 2 > 0 := by
    nlinarith
  have h12 : (x ^ 2 - (-1 + Real.sqrt 5) / 2) * (x ^ 2 - (-1 - Real.sqrt 5) / 2) = 0 := by
    nlinarith [h10, Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h12) with h13 h14
  · -- Case where $x^2 - \frac{\sqrt{5}-1}{2} =0$
    linarith
  · -- Case where $x^2 = \frac{-\sqrt{5}-1}{2}$ which is impossible, need to show contradiction in Lean
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 1), h₀]