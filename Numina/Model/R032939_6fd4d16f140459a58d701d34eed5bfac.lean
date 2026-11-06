import Mathlib

theorem algebra_1697 :
  IsLeast {t : ℝ | ∃ x y z, t = x^2 + y^2 + z^2 ∧ x + 2 * y - z = 6 ∧ x - y + 2 * z = 3} 14 := by 
  constructor
  · -- Show that 14 is in the set
    use 3, 2, 1
    norm_num 
  · -- Show that 14 is the minimum
    intro t ht 
    rcases ht with ⟨x, y, z, h1, h2, h3⟩ 
    have h4 : y = z + 1 := by 
      nlinarith 
    have h5 : x = 4 - z := by 
      linarith [h2, h4]
    have h6 : x^2 + y^2 + z^2 = 3 * z^2 - 6 * z + 17 := by 
      rw [h5, h4]
      nlinarith
    have h7 : 3 * z^2 - 6 * z + 17 ≥ 14 := by 
      nlinarith [sq_nonneg (z - 1)]
    have h8 : x^2 + y^2 + z^2 ≥ 14 := by 
      linarith [h6, h7]
    linarith [h1, h8]