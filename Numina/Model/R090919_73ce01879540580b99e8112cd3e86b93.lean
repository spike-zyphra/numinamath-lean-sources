import Mathlib

theorem algebra_209830 {a b c : ℝ} (h₀ : a > b) (h₁ : (a - b) * (b - c) * (c - a) > 0) :
    a > c := by
  have h2 : a - b > 0 := by linarith
  have h3 : (b - c) * (c - a) > 0 := by
    nlinarith [h₁, h2]
  by_cases h4 : b - c > 0
  · -- Case where b > c
    have h5 : b > c := by linarith
    have h6 : c - a > 0 := by nlinarith [h3, h4]
    linarith
  · -- Case where b ≤ c
    have h7 : b - c ≤ 0 := by linarith
    have h8 : c - a < 0 := by
      nlinarith [h3, h7]
    linarith