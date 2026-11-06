import Mathlib

/-Given that y is an integer and y = 2244 / (x ^ 2 - 12 * x + 67), find the maximum value of y-/
theorem algebra_5683 :
  IsGreatest {y : ℤ | ∃ x : ℝ, y = 2244 / (x ^ 2 - 12 * x + 67)} 72 := by
  constructor
  · -- Let's prove that 72 is in the set
    use 6 + Real.sqrt 6 / 6
    have h : (6 + Real.sqrt 6 / 6 : ℝ) ^ 2 - 12 * (6 + Real.sqrt 6 / 6 : ℝ) + 67 = (2244 : ℝ) / 72 := by
      ring_nf
      have h1 : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0:ℝ) < 6 by norm_num : (6:ℝ) > 0)]
    rw [h]
    norm_num
  · -- Now we need to prove that 72 is the greatest element in this set
    intro y
    rintro ⟨x, hx⟩
    have ineq : (x ^ 2 - 12 * x + 67 : ℝ) ≥ (31 : ℝ) := by
      nlinarith [sq_nonneg (x - 6)]
    have hy: (y: ℝ) ≤ 2244 / 31 := by
        rw [hx]
        rw [div_le_div_iff_of_pos_left]
        simp [ineq]
        norm_num
        nlinarith
        norm_num
    have o: (2244: ℝ) / 31 < 73 := by norm_num
    replace hy: (y: ℝ) < 73 := by
        nlinarith [hy, o] 
    norm_cast at hy
    omega