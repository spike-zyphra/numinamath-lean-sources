import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_226274 :
  IsLeast {z : ℝ | ∃ x y, z = 2 * x * y / (x + y - 1) ∧ x ^ 2 + y ^ 2 = 1} (1 - sqrt 2) := by
  constructor
  · -- Show 1 - sqrt 2 is in the set.
    use (-sqrt 2 / 2), (-sqrt 2 / 2)
    constructor
    · -- Show that ((2 * (-sqrt 2 / 2) * (-sqrt 2 / 2)) / ((-sqrt 2 / 2) + (-sqrt 2 / 2) - 1)) = 1 - sqrt 2
      have ht1 : (2 * (-sqrt 2 / 2) * (-sqrt 2 / 2) : ℝ) = 1 := by
        have ht2 : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        nlinarith
      have ht2 : ((-sqrt 2 / 2 : ℝ) + (-sqrt 2 / 2 : ℝ) - 1) = -sqrt 2 - 1 := by
        ring
      have ht3 : ((2 * (-sqrt 2 / 2) * (-sqrt 2 / 2)) / ((-sqrt 2 / 2) + (-sqrt 2 / 2) - 1) : ℝ) = (1 / (-sqrt 2 - 1) : ℝ) := by
        rw [ht1, ht2]
      have ht4 : (1 / (-sqrt 2 - 1) : ℝ) = (1 - sqrt 2 : ℝ) := by
        have h6 : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        have h7 : (-sqrt 2 - 1 : ℝ) ≠ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
        field_simp [h7, h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
      linarith [ht4, ht3]
    · -- Show that (-sqrt 2 / 2)^2 + (-sqrt 2 / 2)^2 = 1
      have h3 : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h3]
  · -- Show 1 - sqrt 2 is the least
    intro z hz
    rcases hz with ⟨x, y, h_eq, h_con⟩
    by_contra h
    push_neg at h
    by_cases hne : x + y - 1 = 0
    · -- x + y - 1 = 0
      have h3 : x + y = 1 := by linarith
      have h4 : y = 1 - x := by linarith
      rw [h4] at h_con
      have h5 : x * (x - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with hx1 hx2
      · -- x = 0
        have hx0 : x = 0 := by linarith
        have hy1 : y = 1 := by
          rw [hx0] at h4
          linarith
        have h6 : z = (0 : ℝ) := by
          rw [h_eq]
          rw [hx0, hy1]
          norm_num
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), show sqrt 2 > 0 by positivity]
      · -- x - 1 = 0
        have hx1 : x = 1 := by linarith
        have hy0 : y = 0 := by
          rw [hx1] at h4
          linarith
        have h7 : z = (0 : ℝ) := by
          rw [h_eq]
          rw [hx1, hy0]
          norm_num
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), show sqrt 2 > 0 by positivity]
    · -- x + y - 1 ≠ 0
      have h3 : 2 * x * y / (x + y - 1) = (x + y) + 1 := by
        have hne' : x + y - 1 ≠ 0 := hne
        field_simp [hne']
        nlinarith [h_con, sq_nonneg (x - y)]
      have h4 : (x + y) ≥ -sqrt 2 := by
        have h5 : (x + y) ^ 2 ≤ 2 := by
          nlinarith [sq_nonneg (x - y), h_con]
        have h6 : -sqrt 2 ≤ x + y := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
        linarith
      have h5 : 2 * x * y / (x + y - 1) ≥ 1 - sqrt 2 := by
        rw [h3]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
      have h7 : z = 2 * x * y / (x + y - 1) := by linarith [h_eq]
      have h8 : z ≥ 1 - Real.sqrt 2 := by
        linarith [h7, h5]
      linarith