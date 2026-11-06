import Mathlib

theorem algebra_20491 (a b c : ℝ) (h₀ : 4 * a = 6 * b) (h₁ : 24 * b = 8 * c) :
    5 * c = 10 * a := by
  have h2 : b = (2 / 3) * a := by
    linarith
  rw [h2] at h₁
  -- Substitute b in the second equation
  -- 24 * ((2/3) * a) = 8 * c
  -- 16 * a = 8 * c
  -- Therefore c = 2 * a
  have h3 : c = 2 * a := by
    linarith
  -- Therefore, 5 * c = 5 * (2 * a) = 10 * a
  linarith [h3]