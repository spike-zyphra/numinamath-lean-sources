import Mathlib

theorem algebra_171804 (a b c : ℝ) (ha : (2 * a - 3 * c - 4 + b) ≠ 0 ) (hb:(4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16) ≠ 0) : ((6 * a ^ 2 - 2 * b ^ 2 + 6 * c ^ 2 + a * b - 13 * a * c - 4 * b * c - 18 * a - 5 * b + 17 * c + 12) / (4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16)) = (3 * a - 2 * c - 3 + 2 * b) / (2 * a - 3 * c - 4 + b) := by
  have h1 : (4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16) = (2 * a - 3 * c - 4 + b) * (2 * a - b - 3 * c - 4) := by
    ring
  have h2 : (6 * a ^ 2 - 2 * b ^ 2 + 6 * c ^ 2 + a * b - 13 * a * c - 4 * b * c - 18 * a - 5 * b + 17 * c + 12) = (3 * a - 2 * c - 3 + 2 * b) * (2 * a - b - 3 * c - 4) := by 
    ring
  have h3 : (2 * a - b - 3 * c - 4 : ℝ) ≠ 0 := by 
    by_contra h_eq
    have h8 : (4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16) = 0 := by
      have h9 : (4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16) = (2 * a - 3 * c - 4 + b) * (2 * a - b - 3 * c - 4) := h1
      rw [h9]
      rw [show (2 * a - b - 3 * c - 4 : ℝ) = 0 by linarith [h_eq]]
      all_goals
        ring
    have h9 : (4 * a ^ 2 - b ^ 2 + 9 * c ^ 2 - 12 * a * c - 16 * a + 24 * c + 16) ≠ 0 := hb
    contradiction
  rw [h2, h1]
  field_simp [ha, h3, hb]
  <;> ring