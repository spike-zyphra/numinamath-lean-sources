import Mathlib

theorem inequalities_596896 :
    ¬∃ x y z : ℝ, |x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y| := by
  rintro ⟨x, y, z, h₁, h₂, h₃⟩
  have h1' : x^2 < (y - z)^2 := by
    apply sq_lt_sq.mpr
    exact h₁
  have h2' : y^2 < (z - x)^2 := by
    apply sq_lt_sq.mpr
    exact h₂
  have h3' : z^2 < (x - y)^2 := by
    apply sq_lt_sq.mpr
    exact h₃
  nlinarith [sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
            sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
            abs_nonneg (x), abs_nonneg (y - z), abs_nonneg (y), abs_nonneg (z - x), abs_nonneg (z), abs_nonneg (x - y)]