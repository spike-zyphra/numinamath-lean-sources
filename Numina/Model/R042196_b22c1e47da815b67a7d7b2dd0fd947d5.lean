import Mathlib

theorem algebra_9406 : IsLeast {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x * y - x - 2 * y = 0
  ∧ z = x + y} ( 3 + 2 * Real.sqrt 2) := by
  constructor
  · -- Show 3 + 2√2 is achievable with x = 2 + √2 and y = 1 + √2
    use 2 + Real.sqrt 2, 1 + Real.sqrt 2
    constructor
    · -- Show x > 0
      have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by linarith)
      linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show y > 0
      have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by linarith)
      linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show xy - x - 2y = 0
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_pos_of_pos (show 0 < Real.sqrt 2 by positivity)]
    · -- Show z = x + y
      ring
  · -- Show 3 + 2√2 is minimal
    intro z h
    rcases h with ⟨x, y, hx, hy, h_eq, hz⟩
    nlinarith [sq_nonneg (x - (2 + Real.sqrt 2)), sq_nonneg (y - (1 + Real.sqrt 2)), 
          mul_pos hx hy, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg ((x - 2) - Real.sqrt 2), sq_nonneg ((y - 1) - Real.sqrt 2),
          mul_pos (show 0 < Real.sqrt 2 by positivity) (show 0 < Real.sqrt 2 by positivity), Real.sqrt_nonneg 2]