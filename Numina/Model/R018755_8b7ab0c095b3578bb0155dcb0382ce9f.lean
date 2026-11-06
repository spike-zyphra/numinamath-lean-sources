import Mathlib

theorem algebra_167241 {μ : ℝ} (hμ : μ > 0) (V : ℝ) (hV : V = 27 * μ ^ 3)
    (h : V = (1 + 9 / 10) ^ 3 * (27 * μ ^ 3)) :
    (1 + 9 / 10) ^ 3 * (27 * μ ^ 3) / (27 * μ ^ 3) - 1 = 0.08 := by
  have eq1 : (27 * μ ^ 3 : ℝ) > 0 := by 
    positivity
  have eq2 : (27 * μ ^ 3 : ℝ) = (1 + 9 / 10 : ℝ) ^ 3 * (27 * μ ^ 3) := by
    linarith [hV, h]
  have h27 : (1 + 9 / 10 : ℝ) ^ 3 = 1 := by 
    have pos : (27 * μ ^ 3 : ℝ) > 0 := by 
      positivity 
    have eq3 : (27 * μ ^ 3 : ℝ) = (1 + 9 / 10 : ℝ) ^ 3 * (27 * μ ^ 3) := by 
      linarith [hV, h]
    have eq4 : (27 * μ ^ 3 : ℝ) * (1 - (1 + 9 / 10 : ℝ) ^ 3) = 0 := by 
      linarith [eq3]
    cases' (mul_eq_zero.1 eq4) with eq5 eq6
    · -- `27 * μ ^ 3 = 0`, which is a contradiction
      nlinarith [hμ, sq_nonneg (μ ^ 2), sq_nonneg (μ)]
    · -- `1 - (1 + 9/10)^3 = 0`
      linarith 
  have contr : (1 + 9 / 10 : ℝ) ^ 3 ≠ 1 := by norm_num
  contradiction