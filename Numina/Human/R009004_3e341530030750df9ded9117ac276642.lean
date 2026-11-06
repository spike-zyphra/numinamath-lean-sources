import Mathlib

/- Simplify $\sqrt5-\sqrt{20}+\sqrt{45}$. -/
theorem algebra_11600 : Real.sqrt 5 - Real.sqrt 20 + Real.sqrt 45 = 2 * Real.sqrt 5 := by
  -- notice that 20 = 4x5 = 2^2x5, 45 = 9x5 = 3^2 x 5
  have h1: √20 = 2*√5 := by
    have: (20:ℝ) = 2^2 * 5 := by ring
    rw [this]; field_simp
  have h2: √45 = 3*√5 := by
    have: (45:ℝ) = 3^2 * 5 := by ring
    rw [this]; field_simp
  -- so √5 - √20 + √45 = √5 - 2√5 + 3 √5 = 2√5
  rw [h1, h2]; ring