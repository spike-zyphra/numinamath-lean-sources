import Mathlib

/- Given $w$ and $z$ are complex numbers such that $|w+z|=1$ and $|w^2+z^2|=14,$ find the smallest possible value of $|w^3+z^3|.$ -/
theorem algebra_11703 :
  IsLeast {r : ℝ | ∃ w z : ℂ, r = ‖w^3 + z^3‖ ∧ ‖w + z‖ = 1 ∧ ‖w^2 + z^2‖ = 14} (41 / 2) := by
  -- Two goals to prove:
  -- 1. 41/2 is a possible value of |w^3 + z^3|
  -- 2. |w^3 + z^3| is always greater than 41/2
  constructor
  . -- If w + z = 1 and w^2 + z^2 = 14 where w and z are real numbers, then w^3 + z^3 = 41/2
    have ⟨w, z, h1, h2, h3⟩ : ∃ w z : ℝ, w + z = 1 ∧ w^2 + z^2 = 14 ∧ w^3 + z^3 = 41 / 2 := by
      -- w = (1 + √27) / 2, z = (1 - √27) / 2 is a solution
      use (1 + √27) / 2, (1 - √27) / 2
      ring_nf
      norm_num
    use w, z
    -- Just cast everything to complex numbers
    norm_cast
    simp [h1, h2, h3]
  . -- We show that |w^3 + z^3| ≥ 41/2
    rintro r ⟨w, z, rfl, h1, h2⟩
    -- Factorize w^3 + z^3
    rw [show w^3 + z^3 = (w + z) * (w^2 - w * z + z^2) by ring,
    -- Remove w + z
        norm_mul, h1,
    -- Express w^2 - w * z + z^2 in terms of w^2 + z^2 and w + z
        show w^2 - w * z + z^2 = (3 * (w^2 + z^2) - (w + z)^2)/2 by ring]
    simp [-Complex.norm_eq_abs]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    -- Use triangle inequality
    calc ‖3 * (w ^ 2 + z ^ 2) - (w + z) ^ 2‖ ≥ ‖3 * (w ^ 2 + z ^ 2)‖ - ‖(w + z) ^ 2‖ := norm_sub_norm_le _ _
       _ = 3 * ‖w ^ 2 + z ^ 2‖ - ‖w + z‖ ^ 2 := by simp
       _ = 41 := by simp [h1, h2]; norm_num
