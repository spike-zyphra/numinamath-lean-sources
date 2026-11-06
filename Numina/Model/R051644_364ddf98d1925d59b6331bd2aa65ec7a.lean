import Mathlib

theorem algebra_20386 (f : ℝ → ℝ) (hf : f = fun y => -y^2 + 4 * y - 4) :
    ∃! y, f y = 0 := by
  use 2
  constructor
  · -- Show that 2 is indeed a solution
    rw [hf]
    norm_num
  · -- Show that if y is a solution, then y = 2
    intro y hy
    rw [hf] at hy
    simp at hy
    -- We have the equation -y^2 + 4*y - 4 = 0
    -- Let's manipulate it into a perfect square
    have h_eq : -y^2 + 4 * y - 4 = 0 := by linarith
    have h_eq2 : (y - 2) ^ 2 = 0 := by
      nlinarith
    -- From (y - 2)^2 = 0, we can conclude y - 2 = 0
    have h_eq3 : y - 2 = 0 := by
      rw [sq_eq_zero_iff] at h_eq2
      linarith
    -- Therefore y = 2
    linarith