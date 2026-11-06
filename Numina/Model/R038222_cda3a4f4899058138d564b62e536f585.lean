import Mathlib

open Real Set

theorem inequalities_178329 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y) :
    max (x^2) (25 / (y * (x - y))) ≥ 10 := by
  have h1 : y * (x - y) > 0 := by
    have h2 : x - y > 0 := by linarith
    nlinarith
  by_contra h
  push_neg at h
  have h2 : x^2 < 10 := by
    have h3 : max (x^2) (25 / (y * (x - y))) < 10 := h
    cases max_cases (x^2) (25 / (y * (x - y))) with
    | inl h4 =>
      linarith
    | inr h5 =>
      nlinarith
  have h3 : (25 / (y * (x - y))) < 10 := by
    have h4 : max (x^2) (25 / (y * (x - y))) < 10 := h
    cases max_cases (x^2) (25 / (y * (x - y))) with
    | inl h5 =>
      nlinarith
    | inr h6 =>
      linarith
  have h4 : y * (x - y) > 2.5 := by
    have h5 : 0 < y * (x - y) := h1
    have h6 : (25 / (y * (x - y))) < 10 := h3
    have h7 : 25 < 10 * (y * (x - y)) := by
      have h8 : 0 < y * (x - y) := h1
      apply (div_lt_iff₀ h8).mp at h6
      linarith
    linarith
  nlinarith [sq_nonneg (x^2 - 5), sq_nonneg (y - (x - y)), sq_nonneg (y * (x - y) - 2.5), sq_nonneg (x - 3), 
          mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < x - y by nlinarith),
          mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < x by linarith)
          ]