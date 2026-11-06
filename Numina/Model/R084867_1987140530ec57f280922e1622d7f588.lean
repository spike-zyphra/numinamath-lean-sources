import Mathlib

theorem inequalities_2410 (n : ℝ) (h : n^3 < -n) : n < 0 := by
  have h1 : n^3 + n < 0 := by linarith
  have h3 : n * (n^2 + 1) < 0 := by nlinarith
  have h4 : n^2 + 1 > 0 := by
    nlinarith [sq_nonneg n]
  have h5 : n < 0 := by
    apply mul_neg_iff.mp at h3
    cases h3 with
    | inl h6 =>
      nlinarith [sq_nonneg n]
    | inr h7 =>
      linarith
  exact h5