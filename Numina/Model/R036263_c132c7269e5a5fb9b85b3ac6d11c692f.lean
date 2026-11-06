import Mathlib

theorem algebra_183099 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d * (3 / 8) / v = 80) (h₃ : d * (5 / 8) / v = 80) :
    v = 20 := by
  have eq1 : d * (3 / 8) = 80 * v := by
    have h4 : v ≠ 0 := by
      linarith
    field_simp [h4] at h₂
    linarith
  have eq2 : d * (5 / 8) = 80 * v := by
    have h5 : v ≠ 0 := by
      linarith
    field_simp [h5] at h₃
    linarith
  have eq3 : d * (3 / 8) = d * (5 / 8) := by
    linarith [eq1, eq2]
  -- Since d > 0, we can cancel d from both sides
  have eq4 : (3 : ℝ) / 8 = (5 : ℝ) / 8 := by
    apply (mul_left_inj' (show d ≠ 0 by linarith)).mp
    linarith [eq3]
  -- Contradiction: 3/8 = 5/8 is impossible
  linarith