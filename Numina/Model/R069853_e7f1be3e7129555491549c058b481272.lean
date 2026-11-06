import Mathlib

theorem algebra_150933 :
    IsGreatest {z : ℝ | ∃ x y, x + y + z = 5 ∧ x * y + y * z + z * x = 3} (13 / 3) := by 
  constructor 
  · -- Show that 13/3 is attained by an example (x = 1/3, y = 1/3).
    use (1 / 3), (1 / 3)
    constructor
    · norm_num
    · norm_num
  · -- Show that 13/3 is the greatest possible value of z
    intro z hz
    rcases hz with ⟨x, y, h1, h2⟩
    have h3 : x + y = 5 - z := by linarith
    have h4 : (x - y) ^ 2 ≥ 0 := by nlinarith
    have h5 : (5 - z) ^ 2 - 4 * (z ^ 2 - 5 * z + 3) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - (3 - z * (5 - z))), sq_nonneg (x - y), sq_nonneg (x + y - (5 - z)), sq_nonneg (z - 13 / 3), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3)]
    nlinarith 
    all_goals nlinarith
    all_goals norm_num