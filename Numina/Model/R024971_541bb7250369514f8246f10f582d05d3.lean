import Mathlib

open Real Set

theorem inequalities_138826 (a b c : ℝ) (h : a^2 + b^2 + c^2 = l) (hl : l > 0) :
    min (min ((a - b)^2) ((b - c)^2)) ((c - a)^2) ≤ l / 2 := by
  by_contra h1
  push_neg at h1
  have h2 : (a - b) ^ 2 > l / 2 := by
    by_contra h4
    push_neg at h4
    have h3 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (a - b) ^ 2 := by
      simp
    nlinarith
  have h3 : (b - c) ^ 2 > l / 2 := by
    by_contra h4
    push_neg at h4
    have h5 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (b - c) ^ 2 := by
      simp
    nlinarith
  have h4 : (c - a) ^ 2 > l / 2 := by
    by_contra h5
    push_neg at h5
    have h6 : min (min ((a - b) ^ 2) ((b - c) ^ 2)) ((c - a) ^ 2) ≤ (c - a) ^ 2 := by
      simp
    nlinarith
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - 2 * c), sq_nonneg (2 * a - b - c), sq_nonneg (-a + 2 * b - c)]