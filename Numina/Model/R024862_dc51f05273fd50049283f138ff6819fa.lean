import Mathlib

theorem algebra_598061 {x y : ℝ} (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1) : x + y = 0 := by
  have h1 : x + Real.sqrt (x ^ 2 + 1) ≠ 0 := by
    by_contra h22
    have h3 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 0 := by
      rw [h22]
      norm_num
    linarith
  have h2 : y + Real.sqrt (y ^ 2 + 1) = 1 / (x + Real.sqrt (x ^ 2 + 1)) := by
    field_simp [(show x + Real.sqrt (x ^ 2 + 1) ≠ 0 by assumption)]
    <;> nlinarith
  have h7 : (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) = 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by positivity)]
  have h8 : Real.sqrt (x^2 + 1) - x = 1/(x + Real.sqrt (x^2 + 1)) := by
    field_simp [(show x + Real.sqrt (x ^ 2 + 1) ≠ 0 by assumption)]
    <;> nlinarith
  have h9 : y + Real.sqrt (y ^ 2 + 1) = Real.sqrt (x ^ 2 + 1) - x := by
    linarith [h2, h7, h8]
  have h3 : Real.sqrt (x ^ 2 + 1) > 0 := by
    positivity
  have h4 : Real.sqrt (y ^ 2 + 1) > 0 := by
    positivity

  have h10 : x + y = 0 := by
    have eq4 : (x + y) * (Real.sqrt (x ^ 2 + 1) - x) = 0 := by
      nlinarith [sq_nonneg (x + y), sq_nonneg (Real.sqrt (x ^ 2 + 1) - Real.sqrt (y ^ 2 + 1)), sq_nonneg (Real.sqrt (x ^ 2 + 1) + Real.sqrt (y ^ 2 + 1)), sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (y + Real.sqrt (x ^ 2 + 1)), Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (y ^ 2 + 1) by positivity), sq_nonneg (y ^ 2 + 1)]
    cases' (mul_eq_zero.mp eq4) with h101 h102
    · -- Case $x + y = 0$ is the desired result
      linarith
    · -- Case $\sqrt(x^2+1) - x = 0$ contradicts h1
      exfalso
      apply h1
      have h11 : Real.sqrt (x ^ 2 + 1) = x := by
        linarith
      have h12 : (x + Real.sqrt (x ^ 2 + 1)) = (x + x) := by
        rw [h11]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 1 by positivity), sq_nonneg (x ^ 2 + 1 - x^2)]
  exact h10
  all_goals try positivity
  all_goals try nlinarith
  all_goals try nlinarith