import Mathlib

theorem inequalities_312906
    (a b c : ℝ)
    (h₀ : abs a ≥ abs (b + c))
    (h₁ : abs b ≥ abs (c + a))
    (h₂ : abs c ≥ abs (a + b)) :
    a + b + c = 0 := by
  have h3 : a^2 ≥ (b + c)^2 := by 
    apply sq_le_sq.mpr
    linarith [abs_le.mp h₀, abs_nonneg (b + c), abs_nonneg a]
  have h4 : b^2 ≥ (c + a)^2 := by
    apply sq_le_sq.mpr
    linarith [abs_le.mp h₁, abs_nonneg (c + a), abs_nonneg b]
  have h5 : c^2 ≥ (a + b)^2 := by
    apply sq_le_sq.mpr
    linarith [abs_le.mp h₂, abs_nonneg (a + b), abs_nonneg c]
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]