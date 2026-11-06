import Mathlib

/- Compute the unique ordered pair (x,y) of real numbers satisfying the system of equations
x/√(x^2+y^2) - 1/x = 7, y/√(x^2+y^2) + 1/y= 4 -/

theorem algebra_610696 {x y: ℝ}
(uniqueness: ∀ a b: ℝ, (a / Real.sqrt (a^2 + b^2) - 1 / a = 7) ∧  (b / Real.sqrt (a^2 + b^2) + 1 / b = 4) → a = x ∧ b = y)
: (x, y) = (-(13: ℝ) / 96,(13: ℝ) / 40) := by

  -- we first show that these two numbers satisfy the equations --
  specialize uniqueness (-(13: ℝ) / 96) ((13: ℝ) / 40)
  simp at uniqueness
  norm_num

  -- we first compute two sqrts --
  have sqrt28561 : Real.sqrt 28561 = 169 := by
      rw [Real.sqrt_eq_iff_eq_sq, pow_two]
      norm_num
      norm_num
      norm_num
  have sqrt230400 : Real.sqrt 230400 = 480 := by
      rw [Real.sqrt_eq_iff_eq_sq, pow_two]
      norm_num
      norm_num
      norm_num

  -- verify the first equation --
  have eq1: -13 / 96 / √((-13 / 96) ^ 2 + (13 / 40) ^ 2) - 96 / -13 = 7 := by
    norm_num
    simp [sqrt28561, sqrt230400]
    norm_num

    -- verify the second equation --
  have eq2:  13 / 40 / √((-13 / 96) ^ 2 + (13 / 40) ^ 2) + 40 / 13 = 4 := by
    norm_num
    simp [sqrt28561, sqrt230400]
    norm_num

   -- plug eq1 and eq2 --
  simp [eq1,eq2] at uniqueness
  rcases uniqueness with ⟨hx, hy⟩
  constructor
  . rw[← hx]
    norm_num
  . rw[← hy]