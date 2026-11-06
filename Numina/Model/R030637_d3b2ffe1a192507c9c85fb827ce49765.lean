import Mathlib

theorem algebra_22622 : IsLeast { p | ∃(x y z : ℝ), 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z = 2 ∧ p = x ^ 4 + 4 * y ^ 2 + 4 * z ^ 4} 16 := by
  constructor
  · -- Show that 16 is in the set
    use Real.sqrt 2, Real.sqrt 2, 1
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show z > 0
      positivity
    constructor
    · -- Show x * y * z = 2
      have h1 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by 
        calc 
          Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
          _ = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [h1]
    · -- Show p = x^4 + 4*y^2 + 4*z^4
      have h1 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by 
        rw [Real.sq_sqrt] 
        all_goals linarith
      have h2 : (Real.sqrt 2 : ℝ) ^ 4 = (4 : ℝ) := by 
        calc 
          (Real.sqrt 2 : ℝ) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = (2 : ℝ) ^ 2 := by rw [h1]
          _ = (4 : ℝ) := by norm_num 
      nlinarith [h1, h2]
  · -- Show that no value less than 16 is in the set
    intro p hp 
    rcases hp with ⟨x, y, z, hx, hy, hz, h1, he⟩
    have h2 : p = x^4 + 4 * y^2 + 4 * z^4 := by linarith [he]
    have h3 : x^4 + 4 * y^2 + 4 * z^4 ≥ 16 := by 
      nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (z^2 - 1), 
        sq_nonneg (x^2 * z^2 - 2), 
        sq_nonneg (y^2 - 2), 
        sq_nonneg (x * z - Real.sqrt 2), 
        sq_nonneg (y * z - Real.sqrt 2), 
        sq_nonneg (x * y - 2),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    linarith [h2, h3]