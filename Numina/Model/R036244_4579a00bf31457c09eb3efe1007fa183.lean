import Mathlib

theorem inequalities_195329 (x y a : ℝ) (h₀ : x^2 + y^2 = a^2) (h₁ : a ≥ 0) :
    x + y ≤ a * Real.sqrt 2 := by
  have h2 : 2 * a^2 ≥ (x + y) ^ 2 := by
    have h3 : a^2 = x^2 + y^2 := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (a)]
  have h3' : (a * Real.sqrt 2) ^ 2 = 2 * a^2 := by
    calc
      (a * Real.sqrt 2) ^ 2 = a^2 * (Real.sqrt 2) ^ 2 := by ring
      _ = a^2 * 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = 2 * a^2 := by ring
  have h4 : (a * Real.sqrt 2) ^ 2 ≥ (x + y) ^ 2 := by
    linarith [h3', h2]
  have h5 : 0 ≤ a * Real.sqrt 2 := by
    have h6 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [h₁, Real.sqrt_nonneg 2]
  nlinarith [h4, Real.sqrt_nonneg 2, sq_nonneg (a * Real.sqrt 2 - (x + y)), sq_nonneg (x - y), sq_nonneg (x + y - a * Real.sqrt 2)]