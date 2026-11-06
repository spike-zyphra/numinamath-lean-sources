import Mathlib

open Real

theorem algebra_188006 {x : ℝ} (hx : x > 0) (hx1 : x ≠ 1) :
    logb 5 x + logb x 25 = 1 / tan (25 * π / 6) ^ 2 ↔ x = 5 ∨ x = 25 := by
  have h1 : 1 / tan (25 * π / 6) ^ 2 = 3 := by
    have h2 : 25 * π / 6 = 4 * π + π / 6 := by
      linarith [Real.pi_pos]
    rw [h2]
    have htan : tan (4 * π + π / 6) = tan (π / 6) := by
      have h1 : tan (π + π / 6) = tan (π / 6) := by
        rw [show π + π / 6 = π / 6 + Real.pi by ring]
        rw [tan_add_pi]
      have h2 : tan (2 * π + π / 6) = tan (π / 6) := by
        rw [show 2 * π + π / 6 = (π + π / 6) + Real.pi by ring]
        rw [tan_add_pi]
        rw [h1]
      have h3 : tan (3 * π + π / 6) = tan (π / 6) := by
        rw [show 3 * π + π / 6 = (2 * π + π / 6) + Real.pi by ring]
        rw [tan_add_pi]
        rw [h2]
      rw [show 4 * π + π / 6 = (3 * π + π / 6) + Real.pi by ring]
      rw [tan_add_pi]
      rw [h3]
    rw [htan]
    have htanpi6 : tan (π / 6) = 1 / Real.sqrt 3 := by
      have htanpi6 : tan (π / 6) = 1 / Real.sqrt 3 := by
        have h1 : sin (π / 6) = 1 / 2 := by
          exact sin_pi_div_six
        have h2 : cos (π / 6) = Real.sqrt 3 / 2 := by
          exact cos_pi_div_six
        rw [tan_eq_sin_div_cos]
        rw [h1, h2]
        field_simp
      exact htanpi6
    rw [htanpi6]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num : (3:ℝ) > 0), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num : (3:ℝ) ≥ 0)]
  rw [h1]
  constructor
  · -- Forward implication: if the equation holds, then x = 5 or x = 25
    intro h
    have h2 : logb x 25 = 2 / logb 5 x := by
      have h1 : logb x 25 = logb 5 25 / logb 5 x := by
        field_simp [logb]
        all_goals linarith
      have h2 : logb 5 25 = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> (norm_num)
      rw [h2] at h1
      linarith
    have eq1 : logb 5 x + 2 / logb 5 x = 3 := by
      rw [h2] at h
      linarith
    have eq2 : (logb 5 x) ^ 2 - 3 * logb 5 x + 2 = 0 := by
      have hlog : logb 5 x ≠ 0 := by
        by_contra h'
        have h1 : logb 5 x = 0 := by linarith
        have h2 : x = 1 := by
          have h1 : logb 5 x = 0 := by linarith
          rw [logb_eq_iff_rpow_eq] at h1 <;> (try linarith) <;> (try linarith)
        contradiction
      have : (logb 5 x) ^ 2 + 2 = 3 * logb 5 x := by
        field_simp [hlog] at eq1 ⊢
        linarith
      linarith
    have eq3 : (logb 5 x - 1) * (logb 5 x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq3) with h4 h5
    · -- logb 5 x = 1
      have hx1 : x = 5 := by
        have h1 : logb 5 x = 1 := by linarith
        rw [logb_eq_iff_rpow_eq] at h1 <;> (try linarith) <;> (try linarith)
      left
      exact hx1
    · -- logb 5 x = 2
      have hx2 : x = 25 := by
        have h1 : logb 5 x = 2 := by linarith
        rw [logb_eq_iff_rpow_eq] at h1 <;> (try linarith) <;> (try linarith)
      right
      exact hx2
  · -- Backward implication: if x = 5 or x = 25, then the equation holds
    rintro (hx | hx)
    · -- x = 5
      rw [hx]
      have h1 : logb 5 (5 : ℝ) = 1 := by
        norm_num [logb_self_eq_one]
      have h2 : logb 5 (25 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h3 : logb (5 : ℝ) (25 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      field_simp [h1, h3]
      <;> norm_num [h1, h2]
    · -- x = 25
      rw [hx]
      have h1 : logb 5 (25 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : logb (25 : ℝ) (25 : ℝ) = 1 := by
        norm_num [logb_self_eq_one]
      field_simp [h1, h2]
      <;> norm_num [h1, h2]