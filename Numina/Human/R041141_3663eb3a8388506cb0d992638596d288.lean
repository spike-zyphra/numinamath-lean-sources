import Mathlib

theorem algebra_305621 : 
    IsGreatest {z : ℝ | ∃x y, x + y + z = 5 ∧ x * y + y * z + z * x = 3} (13 / 3) := by 
  constructor
  · use (1/3), (1/3)
    norm_num
  · intro z
    rintro ⟨x, y, h₀, h₁⟩
    nlinarith [sq_nonneg (x - (5 - z - y)), sq_nonneg (y - (5 - z - x)), sq_nonneg (x - y),
      sq_nonneg (x + y - (5 - z)), sq_nonneg (x - (5 - z - y)), sq_nonneg (y - (5 - z - x)),
      sq_nonneg (x - y), sq_nonneg (x + y - (5 - z)), sq_nonneg (x - (5 - z - y)),
      sq_nonneg (y - (5 - z - x)), sq_nonneg (x - y), sq_nonneg (x + y - (5 - z))]