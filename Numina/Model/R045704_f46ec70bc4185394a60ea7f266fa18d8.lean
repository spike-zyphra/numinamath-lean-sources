import Mathlib

open scoped Real
open Real Set

theorem algebra_207781 :
  IsLeast {y | ∃ x : ℝ, x ∈ Ioo 0 (π/2) ∧ y = tan x ^ 2 + 2 * tan x + 6 / tan x + 9 / tan x ^ 2 + 4} (10 + 4 * Real.sqrt 3) := by 
  constructor
  · -- Show 10 + 4 * Real.sqrt 3 is in the set
    use Real.pi / 3
    constructor
    · -- Show that π/3 is in (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that the value at π/3 is 10 + 4 * Real.sqrt 3
      have htan : tan (Real.pi / 3) = Real.sqrt 3 := by 
        rw [tan_pi_div_three]
      rw [htan]
      have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      field_simp [h1]
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show 10 + 4 * Real.sqrt 3 is the least
    intro y hy
    rcases hy with ⟨x, ⟨hx1, hx2⟩, hy⟩
    have htan_pos : 0 < tan x := by
      apply tan_pos_of_pos_of_lt_pi_div_two
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have htan_ne_zero : tan x ≠ 0 := by linarith
    have h1 : tan x ^ 2 + 2 * tan x + 6 / tan x + 9 / tan x ^ 2 + 4 ≥ 10 + 4 * Real.sqrt 3 := by 
      have h2 : tan x ^ 2 + 9 / tan x ^ 2 ≥ 6 := by
        have ht1 : tan x > 0 := htan_pos
        have ht2 : tan x ^ 2 + 9 / tan x ^ 2 - 6 ≥ 0 := by
          have ht2_pos : tan x ^ 2 > 0 := by positivity
          have h3 : tan x ^ 2 + 9 / tan x ^ 2 - 6 = ((tan x) ^ 2 - 3) ^ 2 / (tan x ^ 2) := by
            field_simp [ht2_pos]
            ring
          rw [h3]
          have ht3_pos : (tan x) ^ 2 > 0 := by positivity
          positivity
        linarith
      have h3 : 2 * tan x + 6 / tan x ≥ 4 * Real.sqrt 3 := by
        have ht1 : tan x > 0 := htan_pos
        have ht2 : (2 * tan x + 6 / tan x) - 4 * Real.sqrt 3 ≥ 0 := by
          have ht2_pos : tan x > 0 := ht1
          have h4 : (2 * tan x + 6 / tan x) - 4 * Real.sqrt 3 = (2 * (tan x) ^ 2 + 6 - 4 * Real.sqrt 3 * tan x) / tan x := by 
            field_simp [show tan x ≠ 0 by linarith]
            <;> ring
          rw [h4] at *
          have ht5_pos : tan x > 0 := ht1
          have ht1_pos : 2 * (tan x) ^ 2 + 6 - 4 * Real.sqrt 3 * tan x ≥ 0 := by 
            nlinarith [sq_nonneg (tan x - Real.sqrt 3), sq_nonneg (2 * tan x - 2 * Real.sqrt 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos (show 0 < (1 : ℝ) by norm_num) (show 0 < (1 : ℝ) by norm_num), sq_nonneg (tan x), sq_nonneg (tan x * (Real.sqrt 3))
              ]
          apply div_nonneg
          linarith
          linarith
        linarith
      have h4 : tan x ^ 2 + 2 * tan x + 6 / tan x + 9 / tan x ^ 2 + 4 ≥ 10 + 4 * Real.sqrt 3 := by 
        have h5 : tan x ^ 2 + 2 * tan x + 6 / tan x + 9 / tan x ^ 2 + 4 = (tan x ^ 2 + 9 / tan x ^ 2) + (2 * tan x + 6 / tan x) + 4 := by 
          field_simp [htan_ne_zero]
          <;> ring 
        rw [h5]
        linarith [h2, h3, Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
      linarith
    linarith [h1, hy]