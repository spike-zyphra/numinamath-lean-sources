import Mathlib

theorem algebra_248628 (a b : ℝ) (h : ∀ x ∈ Set.Icc 0 1, |a * x + b| ≤ 1) :
    |20 * a + 14 * b| + |20 * a - 14 * b| ≤ 80 := by
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h (1 / 2) (by norm_num)
  have h4 := h (2 / 3) (by norm_num)
  have h5 := h (1 / 3) (by norm_num)
  cases' abs_cases (20 * a + 14 * b) with h16 h16 <;> 
    cases' abs_cases (20 * a - 14 * b) with h17 h17 <;> 
      linarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]