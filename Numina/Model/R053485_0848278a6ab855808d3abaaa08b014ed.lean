import Mathlib

theorem algebra_5269 :
  IsLeast {t : ℝ | ∃ x y, t = 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 176 * x + 264 * y + 2021} 85 := by 
  constructor 
  · -- Show that 85 is achievable, i.e., there exist real numbers x and y such that the expression equals 85 
    use -22, 0
    norm_num 
  · -- Show that 85 is the least such value, i.e., there is no smaller value in the set 
    intro t ht 
    rcases ht with ⟨x, y, hxy⟩ 
    have h : 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 176 * x + 264 * y + 2021 = (2 * x + 3 * y + 44)^2 + 85 := by 
      ring 
    rw [h] at hxy 
    have h1 : (2 * x + 3 * y + 44)^2 ≥ 0 := by 
      exact sq_nonneg (2 * x + 3 * y + 44)
    linarith