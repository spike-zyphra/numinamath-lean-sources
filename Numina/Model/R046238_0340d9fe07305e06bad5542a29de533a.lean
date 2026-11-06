import Mathlib

theorem algebra_321386 (x y z : ℝ) :
    x * y + y * z + z * x = 1 ∧ 5 * x + 8 * y + 9 * z = 12 ↔
    (x = 1 ∧ y = 1 / 2 ∧ z = 1 / 3) := by
  constructor
  · -- Assume (x * y + y * z + z * x = 1 ∧ 5 * x + 8 * y + 9 * z = 12), prove (x = 1 ∧ y = 1 / 2 ∧ z = 1 / 3)
    rintro ⟨h1, h2⟩
    have h3 : (x - 1) ^ 2 + (y - 1 / 2) ^ 2 + (z - 1 / 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 3), 
        sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1)]
    have hx1 : x - 1 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 3)]
    have hx2 : x = 1 := by linarith
    -- Now using hx2, we can substitute x = 1 into the other equations to solve for y and z.
    have hy1 : y - 1 / 2 = 0 := by
      rw [show x = 1 by linarith] at h1 h2
      nlinarith [sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 3), 
          sq_nonneg (z + 1 / 3), sq_nonneg (y + 1 / 2)]
    have hy2 : y = 1 / 2 := by linarith
    -- Then using h2 to solve for z.
    have h4 : z - 1 / 3 = 0 := by
      rw [show x = 1 by linarith, show y = 1 / 2 by linarith] at h2
      linarith
    have h5 : z = 1 / 3 := by linarith
    constructor
    · exact hx2
    constructor
    · exact hy2
    · exact h5
  · -- Assume (x = 1 ∧ y = 1 / 2 ∧ z = 1 / 3), prove both equations.
    rintro ⟨hx, hy, hz⟩
    constructor
    · -- x * y + y * z + z * x = 1
      rw [hx, hy, hz]
      norm_num
    · -- 5 * x + 8 * y + 9 * z = 12
      rw [hx, hy, hz]
      norm_num