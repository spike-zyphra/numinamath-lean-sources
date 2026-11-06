import Mathlib

theorem algebra_228260 {a b c d : ℝ} (h : a^2 + d^2 - 2 * (a * b + b * c + c * d - b^2 - c^2) = 0) :
    a = b ∧ b = c ∧ c = d := by 
  have h1 : (a - b) ^ 2 + (d - c) ^ 2 + (b - c) ^ 2 = 0 := by linarith
  have h2 : (a - b) ^ 2 = 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (d - c), sq_nonneg (b - c)]
  have h3 : (d - c) ^ 2 = 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (d - c), sq_nonneg (b - c)]
  have h4 : (b - c) ^ 2 = 0 := by
    linarith [sq_nonneg (a - b), sq_nonneg (d - c), sq_nonneg (b - c)]
  have h5 : a - b = 0 := by
    rwa [sq_eq_zero_iff] at h2
  have h6 : d - c = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have h7 : b - c = 0 := by
    rwa [sq_eq_zero_iff] at h4
  exact ⟨by linarith, by linarith, by linarith⟩