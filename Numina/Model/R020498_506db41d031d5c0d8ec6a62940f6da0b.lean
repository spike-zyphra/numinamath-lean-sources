import Mathlib

open scoped BigOperators

theorem algebra_298082 {a b : ℕ → ℝ}
  (ha1 : a 1 = 1) (hb1 : b 1 = 2)
  (han : ∀ n, a (n + 1) = (1 + a n + a n * b n) / b n)
  (hbn : ∀ n, b (n + 1) = (1 + b n + a n * b n) / a n) :
  a 2008 < 5 := by
  have ha0 := han 0
  simp [ha1] at ha0
  have hb0 := hbn 0
  simp [hb1] at hb0
  by_cases h1 : a 0 = 0
  · 
    rw [h1] at hb0
    norm_num at hb0
  · 
    by_cases h2 : b 0 = 0
    · 
      rw [h2] at ha0
      norm_num at ha0
    · 
      field_simp [h1, h2] at ha0 hb0
      nlinarith [sq_nonneg (a 0 - 1), sq_nonneg (b 0 - 2), sq_nonneg (a 0 - 2), sq_nonneg (b 0 - 1)]