import Mathlib

theorem inequalities_266332 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
    (|a - b| ≤ Real.sqrt 2 / 2 ∨ |b - c| ≤ Real.sqrt 2 / 2 ∨ |c - a| ≤ Real.sqrt 2 / 2) := by
  by_contra h1
  push_neg at h1
  have h2 : |a - b| > Real.sqrt 2 / 2 := h1.1
  have h3 : |b - c| > Real.sqrt 2 / 2 := h1.2.1
  have h4 : |c - a| > Real.sqrt 2 / 2 := h1.2.2
  have h5 : (a - b) ^ 2 > 1 / 2 := by
    by_contra h5
    push_neg at h5
    have h5' : |a - b| ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (a - b) with h6 h6
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h6, h5]
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h6, h5]
    linarith
  have h6 : (b - c) ^ 2 > 1 / 2 := by
    by_contra h6
    push_neg at h6
    have h6' : |b - c| ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (b - c) with h7 h7
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h7, h6]
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h7, h6]
    linarith
  have h7 : (c - a) ^ 2 > 1 / 2 := by
    by_contra h7
    push_neg at h7
    have h7' : |c - a| ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (c - a) with h8 h8
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h8, h7]
      · nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), h8, h7]
    linarith
  have h8 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 3 / 2 := by
    linarith [h5, h6, h7]
  have h9 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) := by
    ring
  rw [h] at h9
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]