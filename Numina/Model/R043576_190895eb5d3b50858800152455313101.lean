import Mathlib

theorem algebra_65945 :
    IsGreatest {z | ∃ x y : ℝ, z = |x - y| ∧ x ^ 2 + y ^ 2 = 2023 ∧ (x - 2) * (y - 2) = 3} (13 * Real.sqrt 13) := by
  constructor
  · -- Show that 13 * Real.sqrt 13 is in the set.
    use (-43 + 13 * Real.sqrt 13) / 2, (-43 - 13 * Real.sqrt 13) / 2
    constructor
    · -- Show |x - y| = 13 * Real.sqrt 13
      have h1 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
      have h2 : ((-43 + 13 * Real.sqrt 13 : ℝ) / 2 - (-43 - 13 * Real.sqrt 13 : ℝ) / 2 : ℝ) = 13 * Real.sqrt 13 := by
        linarith
      rw [h2]
      all_goals
        simp [abs_of_nonneg, mul_nonneg, Real.sqrt_nonneg]
    constructor
    · -- Show x^2 + y^2 = 2023
      nlinarith [Real.sqrt_pos.mpr (show 13 > 0 by norm_num : (13 : ℝ) > 0), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    · -- Show (x - 2) * (y - 2) = 3
      nlinarith [Real.sqrt_pos.mpr (show 13 > 0 by norm_num : (13 : ℝ) > 0), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  · -- Show that 13 * Real.sqrt 13 is greatest.
    intro z hz
    rcases hz with ⟨x, y, hz_eq, h1, h2⟩
    have h3 : (x - y) ^ 2 ≤ 2197 := by
      nlinarith [sq_nonneg (x + y + 43), sq_nonneg (x * y + 87), sq_nonneg (x - y), sq_nonneg (x + y - (-43)), sq_nonneg (x * 2 + y * 2 - 2), sq_nonneg ((x * y) + 87), Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h4 : |x - y| ≤ 13 * Real.sqrt 13 := by
      have h6 : (x - y) ^ 2 ≤ 2197 := h3
      have h7 : |x - y| ^ 2 ≤ 2197 := by
        have h8 : |x - y| ^ 2 = (x - y) ^ 2 := by
          simp [sq_abs]
        linarith [h8, h6]
      have h8 : |x - y| ≤ Real.sqrt 2197 := by
        apply Real.le_sqrt_of_sq_le
        linarith
      have h9 : Real.sqrt 2197 = 13 * Real.sqrt 13 := by
        calc
          Real.sqrt 2197 = Real.sqrt (13 ^ 3) := by norm_num
          _ = Real.sqrt (13 ^ 2 * 13) := by ring_nf
          _ = Real.sqrt (13 ^ 2) * Real.sqrt 13 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (13 : ℝ) * Real.sqrt 13 := by
            rw [Real.sqrt_sq (by norm_num)]
      linarith [h8, h9]
    linarith [hz_eq, h4]