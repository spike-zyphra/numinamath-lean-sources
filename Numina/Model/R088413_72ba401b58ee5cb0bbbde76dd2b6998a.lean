import Mathlib

theorem algebra_937 {a b c : ℕ} (ha : a ^ 2 + b ^ 2 + c ^ 2 + 42 < 4 * a + 4 * b + 12 * c) (hb : a ^ 2 - a - 2 > 0) :
    (1 / a : ℚ) + 1 / b + 1 / c = 1 := by 
  have h1 : a ≤ 4 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 6 : ℤ)]
  have h2 : b ≤ 4 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 6 : ℤ)]
  have h3 : c ≤ 8 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a - 3 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 6 : ℤ)]
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> norm_num at ha hb ⊢
  <;> all_goals
    norm_num