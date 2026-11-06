import Mathlib

theorem inequalities_33494 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a^2 + b^2 + c^2 = 2) :
    |a - b| ≥ 1 ∨ |b - c| ≥ 1 ∨ |c - a| ≥ 1 := by
  by_contra h
  push_neg at h
  have h2 : |a - b| < 1 := by
    linarith [h.1]
  have h3 : |b - c| < 1 := by
    linarith [h.2.1]
  have h4 : |c - a| < 1 := by
    linarith [h.2.2]

  have h21 : (a - b) ^ 2 < 1 := by
    nlinarith [abs_lt.mp h2]
  have h22 : (b - c) ^ 2 < 1 := by
    nlinarith [abs_lt.mp h3]
  have h23 : (c - a) ^ 2 < 1 := by
    nlinarith [abs_lt.mp h4]

  have h24 : a^2 + b^2 + c^2 = 2 := h₁
  have h25 : a + b + c = 2 := h₀

  have h26 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 2 := by 
    nlinarith

  nlinarith [abs_nonneg (a - b), abs_nonneg (b - c), 
    abs_nonneg (c - a), 
      abs_lt.mp h2, abs_lt.mp h3, abs_lt.mp h4, 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]