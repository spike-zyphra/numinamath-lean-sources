import Mathlib

theorem inequalities_603061 (x y z : ℝ) (hx : x < 0) (hy : y < 0) (hz : z < 0) :
    (x^2 - y^2 - x * y)^2 + (y^2 - z^2 - y * z)^2 + (z^2 - x^2 - z * x)^2 ≥
    y^2 * z^2 + z^2 * x^2 + x^2 * y^2 ∧
    ((x^2 - y^2 - x * y)^2 + (y^2 - z^2 - y * z)^2 + (z^2 - x^2 - z * x)^2 =
     y^2 * z^2 + z^2 * x^2 + x^2 * y^2 ↔ x = y ∧ y = z) := by
  constructor
  · -- First part: proving the inequality
    nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos (show 0 < (-x) by linarith) (show 0 < (-y) by linarith), mul_pos (show 0 < (-y) by linarith) (show 0 < (-z) by linarith), mul_pos (show 0 < (-z) by linarith) (show 0 < (-x) by linarith)]
  · -- Second part: proving the equality condition
    constructor
    · -- Assume equality holds, prove x = y ∧ y = z
      intro heq
      have h1 : (x - y) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
                mul_pos (show 0 < (-x) by linarith) (show 0 < (-y) by linarith), mul_pos (show 0 < (-y) by linarith) (show 0 < (-z) by linarith), mul_pos (show 0 < (-z) by linarith) (show 0 < (-x) by linarith)]
      have h2 : x - y = 0 := by
        nlinarith
      -- Show that (x=y) from x - y = 0
      have hx1 : x = y := by linarith
      have h3 : (y - z) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
                mul_pos (show 0 < (-x) by linarith) (show 0 < (-y) by linarith), mul_pos (show 0 < (-y) by linarith) (show 0 < (-z) by linarith), mul_pos (show 0 < (-z) by linarith) (show 0 < (-x) by linarith)]
      have h4 : y - z = 0 := by
        nlinarith
      have hy1 : y = z := by linarith
      exact ⟨hx1, hy1⟩
    · -- Assume x = y ∧ y = z, prove equality holds
      rintro ⟨rfl, rfl⟩
      nlinarith