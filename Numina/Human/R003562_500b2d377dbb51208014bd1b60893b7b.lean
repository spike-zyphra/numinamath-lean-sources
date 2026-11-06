import Mathlib

open Real

/- $\log _{x} 4+2 \log _{4 x} 4+3 \log _{16 x} 4=0$.
-/
theorem algebra_195930 (x : ℝ) (hx : 0 < x) (hx₀ : x ≠ 1 / 4) :
    3 * Real.logb x 4 + 2 * Real.logb (4 * x) 4 + 3 * Real.logb (16 * x) 4 = 0 ↔
    x = 1 / 8 ∨ x = 1 / 2 := by
  -- We need to compute these specific log values for computations
  have log_eighth_four : logb (1 / 8) 4 = - 2 / 3 := by
    rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) (by positivity)]
    rw [one_div, inv_rpow (by positivity), show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← rpow_mul (by positivity)]
    norm_num
  have log_half_four : logb (1 / 2) 4 = - 2 := by
    rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) (by positivity)]
    rw [one_div, inv_rpow (by positivity)]
    norm_num
  have log_two_four : logb 2 4 = 2 := by
    rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) (by positivity)]
    norm_num
  have log_eight_four : logb 8 4 = 2 / 3 := by
    rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) (by positivity)]
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← rpow_mul (by positivity)]
    norm_num
  have log_four_sixteen : logb 4 16 = 2 := by
    rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) (by positivity)]
    norm_num
  constructor
  · -- Show that 1 / 8 and 1 / 2 are the only solutions
    intro hx'
    -- Introduce a substitution
    let y := logb 4 x
    conv at hx' =>
      -- Swap order of arguments
      rw [← inv_logb, ← inv_logb 4, ← inv_logb 4]
      repeat rw [logb_mul (by positivity) (by positivity)]
      -- Fill in explicit values
      rw [logb_self_eq_one (by linarith), log_four_sixteen]
      -- Rewrite in terms of y
      change 3 * y⁻¹ + 2 * (1 + y)⁻¹ + 3 * (2 + y)⁻¹ = 0
    -- We need to show this to clear denominators
    have : y ≠ 0 ∧ 1 + y ≠ 0 ∧ 2 + y ≠ 0 := by
      constructor
      · intro hy
        rw [hy] at hx'
        linarith
      constructor
      · -- In lean, logb 1 x is defined to be 0, which in our case, would actually make y = -1 yield a valid solution. To counteract this, we explicitly include the condition that x ≠ 1 / 4 in the formalization
        intro hy
        have : y = -1 := by linarith
        rw [logb_eq_iff_rpow_eq (by positivity) (by norm_num) hx, rpow_neg_one, ← one_div] at this
        -- We get a contradiction to hx₀
        tauto
      intro hy
      have : y = -2 := by linarith
      rw [this] at hx'
      norm_num at hx'
    conv at hx' =>
      -- Clear denominators
      rw [← mul_right_inj' this.1, ← mul_right_inj' this.2.1, ← mul_right_inj' this.2.2]
      repeat rw [mul_add y]
      repeat rw [mul_add (1 + y)]
      repeat rw [mul_add (2 + y)]
      rw [← mul_assoc y, mul_comm y 3, mul_assoc , mul_inv_cancel₀ (by tauto)]
      rw [← mul_assoc (1 + y) y, mul_comm (1 + y) y, mul_assoc y, ← mul_assoc (1 + y) 2, mul_comm (1 + y) 2, mul_assoc, mul_inv_cancel₀ (by tauto) ]
      rw [← mul_assoc (2 + y) (1 + y) (y * _), mul_comm (2 + y) (1 + y), mul_assoc (1 + y), ← mul_assoc (2 + y) y (3 * _), mul_comm (2 + y) y, mul_assoc, ← mul_assoc (2 + y) 3, mul_comm (2 + y) 3, mul_assoc, mul_inv_cancel₀ (by tauto) ]
      simp
    -- Yield a quadratic
    suffices 4 * y ^ 2 + 8 * y + 3 = 0 by
      -- Factor the quadratic
      suffices (2 * y + 3) * (2 * y + 1) = 0 by
        -- Solve for y from the factorization
        have y_vals : y = - 3 / 2 ∨ y = - 1 / 2 := by
          rw [mul_eq_zero] at this
          rcases this with hy | hy
          · left; linarith
          right; linarith
        -- Solve for x in terms of y
        have x_formula : x = 4 ^ y := (rpow_logb (by positivity) (by norm_num) hx).symm
        rw [x_formula]
        -- Solve for the respective x values
        rcases y_vals with hy | hy
        · -- Case when y = - 3 / 2
          left
          rw [hy, neg_div, rpow_neg (by positivity), one_div, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by positivity), mul_div_cancel₀ 3 (by norm_num)]
          norm_num
        -- Case when y = - 1 / 2
        right
        rw [hy, neg_div, rpow_neg (by positivity), one_div, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by positivity), mul_inv_cancel₀ (by norm_num)]
        simp
      -- Prove factorization
      linarith
    -- Simplify to the desired quadratic
    linarith
  -- Show that 1 / 8 and 1 / 2 solve the equation
  intro hx
  rcases hx with rfl | rfl
  -- Plug in the values
  all_goals
    norm_num
    linarith