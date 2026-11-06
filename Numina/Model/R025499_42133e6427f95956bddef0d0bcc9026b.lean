import Mathlib

open Real Set
open scoped Real

theorem inequalities_307783 (x : ℝ) (hx : 0 < x ∧ x < π/2) :
    tan x ≥ 4 * (tan x) ^ ((1 : ℝ)/4) - 3 := by
  have htan_pos : tan x > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals 
      linarith [Real.pi_pos, hx.1, hx.2]
  have h1 : tan x ^ ((1 : ℝ) / 4) > 0 := by
    have h5 : tan x > 0 := htan_pos
    have h7 : tan x ^ ((1 : ℝ) / 4) > 0 := by
      apply Real.rpow_pos_of_pos
      linarith
    assumption
  have ht2 : tan x ^ ((1 : ℝ) / 4) ≥ 0 := by 
    linarith [show tan x ^ ((1 : ℝ) / 4) ≥ 0 by positivity]
  have h9 : (tan x ^ ((1 : ℝ) / 4)) ^ 4 > 0 := by
    have h20 : tan x ^ ((1 : ℝ) / 4) > 0 := h1
    positivity
  have h10 : tan x = ((tan x ^ ((1 : ℝ)/4)) ^ 4) := by
    have h99 : tan x = ((tan x ^ ((1 : ℝ)/4)) ^ (4 : ℝ)) := by 
      rw [← Real.rpow_mul]
      norm_num
      all_goals
        linarith [show tan x > 0 by linarith [htan_pos]]
    exact_mod_cast h99
  have heq : (tan x ^ ((1 : ℝ)/4) ) ^ 4 ≥ 4 * (tan x ^ ((1 : ℝ)/4)) - 3 := by
    have h30 : (tan x ^ ((1 : ℝ)/4) : ℝ) ≥ 0 := by linarith
    have h5 : (tan x ^ ((1 : ℝ)/4) ) ^ 4 - (4 * (tan x ^ ((1 : ℝ)/4)) - 3) ≥ 0 := by
      have pos : 0 ≤ tan x ^ ((1 : ℝ) / 4) := by positivity
      nlinarith [sq_nonneg ((tan x ^ ((1 : ℝ)/4) : ℝ ) - 1), sq_nonneg ((tan x ^ ((1 : ℝ)/4) : ℝ ) ^ 2 + 2 * (tan x ^ ((1 : ℝ)/4) : ℝ ) + 3), sq_nonneg ((tan x ^ ((1 : ℝ)/4) : ℝ ) + 1), mul_nonneg (show 0 ≤ ((tan x ^ ((1 : ℝ)/4) : ℝ ) - 1) ^ 2 by positivity) (show 0 ≤ (tan x ^ ((1 : ℝ)/4) : ℝ ) + 1 by linarith ) ]
    linarith
  linarith [ show tan x = ((tan x ^ ((1 : ℝ)/4)) ^ 4) by linarith [h10], heq ]