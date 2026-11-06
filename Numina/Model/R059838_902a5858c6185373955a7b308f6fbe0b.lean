import Mathlib

theorem algebra_64649 (a b c d : ℝ) (h : a * d - b * c = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * c + b * d ≠ 0 ∧
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * c + b * d ≠ 1 ∧
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * c + b * d ≠ -1 := by
  constructor
  · -- Show that $Q \neq 0$.
    by_contra h1
    have h2 : (a + c) ^ 2 + (b + d) ^ 2 = 0 := by
      nlinarith
    have h3 : a + c = 0 := by
      nlinarith [sq_nonneg (a + c), sq_nonneg (b + d)]
    have h4 : b + d = 0 := by
      nlinarith [sq_nonneg (a + c), sq_nonneg (b + d)]
    have ha : a = -c := by linarith
    have hb : b = -d := by linarith
    rw [ha, hb] at h
    nlinarith
  constructor
  · -- Show that $Q \neq 1$.
    by_contra h2
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a - d), sq_nonneg (b + c)]
  · -- Show that $Q \neq -1$.
    by_contra h3
    nlinarith [sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a - c), sq_nonneg (b - d)]