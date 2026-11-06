import Mathlib

/-Let $P$ be a point on the hyperbola $x^2 + 8xy + 7y^2 = 225.$  Find the shortest possible distance from the origin to $P.$-/
theorem algebra_20270 :
    IsLeast {d | ∃ x y : ℝ, d = Real.sqrt (x^2 + y^2) ∧ x^2 + 8 * x * y + 7 * y^2 = 225} 5 := by
  constructor
  · -- First, we'll show that 5 belongs to the set by finding specific points on the hyperbola that are 5 units from the origin.
    use Real.sqrt 5, 2 * Real.sqrt 5
    constructor
    · -- Show distance is 5
      have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h2 : (2 * Real.sqrt 5 : ℝ) ^ 2 = 4 * (Real.sqrt 5 ^ 2) := by ring
      rw [h2, h1]
      have h3 : Real.sqrt (5 + (4 * 5 : ℝ)) = 5 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      linarith [h3]
    · -- Show point is on hyperbola
      have h1 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0:ℝ) < (5:ℝ) by norm_num : (5:ℝ) > 0)]
  · -- Now we need to prove that 5 is a lower bound for all distances in the set.
    intro d hd
    rcases hd with ⟨x, y, h_eq, h_hyperbola⟩
    have h : x^2 + y^2 ≥ 25 := by
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (2 * x + y),
        mul_self_nonneg (x + 2 * y), mul_self_nonneg (2 * x + y),
        sq_nonneg (x - Real.sqrt 5), sq_nonneg (y - 2 * Real.sqrt 5),
        sq_nonneg (x + Real.sqrt 5), sq_nonneg (y + 2 * Real.sqrt 5),
        Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num : (5:ℝ) ≥ 0),
        h_hyperbola]
    have h' : Real.sqrt (x^2 + y^2) ≥ 5 := by
      have h1 : x^2 + y^2 ≥ 25 := h
      have h2 : Real.sqrt (x^2 + y^2) ≥ Real.sqrt (25 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h3 : Real.sqrt (25 : ℝ) = 5 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith [h2, h3]
    rw [h_eq] at *
    linarith [h']