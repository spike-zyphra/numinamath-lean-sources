import Mathlib

theorem algebra_282058 (a b c : ℝ) (h : ∀ x : ℝ, |x| ≤ 1 → |a * x ^ 2 + b * x + c| ≤ 1) :
    ∀ x : ℝ, |x| ≤ 1 → |a * x + b| ≤ 2 := by
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1 : ℝ) (by norm_num)
  have h3 := h (0 : ℝ) (by norm_num)
  have h4 := h x hx
  have h1' : -1 ≤ a + b + c := by linarith [abs_le.mp h1]
  have h1'' : a + b + c ≤ 1 := by linarith [abs_le.mp h1]
  have h2' : -1 ≤ a - b + c := by linarith [abs_le.mp h2]
  have h2'' : a - b + c ≤ 1 := by linarith [abs_le.mp h2]
  have h3' : -1 ≤ c := by linarith [abs_le.mp h3]
  have h3'' : c ≤ 1 := by linarith [abs_le.mp h3]
  have h4' : -1 ≤ a * x ^ 2 + b * x + c := by linarith [abs_le.mp h4]
  have h4'' : a * x ^ 2 + b * x + c ≤ 1 := by linarith [abs_le.mp h4]
  have hx2 : -1 ≤ x := by linarith [abs_le.mp hx]
  have hx3 : x ≤ 1 := by linarith [abs_le.mp hx]
  have hx4 : x ^ 2 ≤ 1 := by nlinarith
  apply abs_le.mpr
  constructor
  · -- Prove lower bound: -2 ≤ a * x + b
    nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  · -- Prove upper bound: a * x + b ≤ 2
    nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]