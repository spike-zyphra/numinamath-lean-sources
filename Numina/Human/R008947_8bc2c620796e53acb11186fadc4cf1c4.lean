import Mathlib

/- Let $(x,y)$ be an ordered pair of real numbers that satisfies the equation $x^2+y^2=14x+48y$. What is the minimum value of $x$? -/
theorem algebra_21283 : IsLeast {x : ℝ | ∃ y : ℝ, x ^ 2 + y ^ 2 = 14 * x + 48 * y} (-18) := by
  constructor
  · -- $18$ is a possible value
    use 24
    norm_num
  · -- $18$ is the least such
    intro x xin
    rcases xin with ⟨y, h⟩
    -- complete the spuare
    apply sub_eq_zero_of_eq at h
    have eq : x ^ 2 + y ^ 2 - (14 * x + 48 * y) = (x - 7) ^2 + (y - 24) ^ 2 - 625 := by
      ring
    rw [eq] at h
    nlinarith
