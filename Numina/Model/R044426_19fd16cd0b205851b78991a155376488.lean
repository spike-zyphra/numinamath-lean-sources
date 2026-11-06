import Mathlib

open Real

theorem algebra_18968 :
    IsLeast {r : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z * (x + y + z) = 1 ∧ r = (x + y) * (y + z)} 2 := by 
  constructor
  · -- Show 2 is in the set
    use 1, Real.sqrt 2 - 1, 1
    constructor
    · norm_num
    constructor
    · -- Show that sqrt(2) - 1 > 0
      have h1 : 1 < Real.sqrt 2 := by
        rw [Real.lt_sqrt]
        all_goals norm_num
      have h2 : Real.sqrt 2 - 1 > 0 := by
        linarith [h1]
      linarith
    constructor
    · norm_num
    constructor
    · -- Show the constraint is satisfied
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Show r = 2
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show 2 is the minimum value
    intro r hr
    rcases hr with ⟨x, y, z, hx, hy, hz, h1, hr⟩
    nlinarith [sq_nonneg (y * (x + y + z) - x * z), sq_nonneg (x * z - 1), sq_nonneg (y * (x + y + z) - 1), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos (mul_pos hx hy) hz 
    ]