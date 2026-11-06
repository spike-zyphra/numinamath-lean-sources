import Mathlib

open Real

/- What is the product of all real numbers x such that the distance on the number line between
logb 6 x and logb 6 9 is twice the distance on the number line between logb 6 10 and 1?

(A) 10(B) 18(C) 25(D) 36(E) 81 -/
theorem algebra_95090 {x : ℝ} (hx : 0 < x) :
abs (logb 6 x - logb 6 9) = 2 * abs (logb 6 10 - 1) ↔ x = 25 ∨ x = 81 / 25 := by
  -- Solving for x using logarithm rules and absolute value rules
  constructor
  . intro h
    rw [← Real.logb_self_eq_one (by norm_num: (1:ℝ) < 6), ← abs_two, ← abs_mul] at h
    rw [← Real.logb_div (by exact ne_of_gt hx) (by norm_num), ← Real.logb_div (by norm_num) (by norm_num)] at h
    rw [(by norm_num : (2: ℝ) = (2: ℕ)), ← Real.logb_pow 6 (10/6) (2: ℕ), abs_eq_abs] at h
    -- Handling the two cases for absolute value corresponding to the side of the number line x is on relative to logb 6 9
    cases h
    -- Case x on the right of logb 6 9 → x = 25
    . have h : logb 6 (x / 9) = logb 6 ((10 / 6) ^ 2) := by assumption
      apply Or.inl
      norm_num at h
      apply Real.logb_injOn_pos (by norm_num : 1 < (6:ℝ))
      . assumption
      . norm_num
      rw [logb_div, logb_div, sub_left_inj] at h
      assumption
      . norm_num
      . norm_num
      . exact ne_of_gt hx
      . norm_num
    -- Case x on the left of logb 6 9 → x = 81/25
    . have h : logb 6 (x / 9) = -logb 6 ((10 / 6) ^ 2) := by assumption
      apply Or.inr
      rw [← Real.logb_inv] at h
      norm_num at h
      apply Real.logb_injOn_pos (by norm_num : 1 < (6:ℝ))
      . assumption
      . norm_num
      rw [logb_div, sub_eq_iff_eq_add', ← logb_mul] at h
      norm_num at h
      assumption
      . norm_num
      . norm_num
      . exact ne_of_gt hx
      . norm_num
  -- Verifying that the two values of x satisfy the original equation
  . intro h
    cases h
    -- Case x = 25
    . have h : x = 25 := by assumption
      rw [h]
      rw [← Real.logb_self_eq_one (by norm_num: (1:ℝ) < 6)]
      rw [← Real.logb_div (by norm_num) (by norm_num), ← Real.logb_div (by norm_num) (by norm_num)]
      norm_num
      rw [← abs_two, ← abs_mul, (by norm_num : (2: ℝ) = (2: ℕ)), ← Real.logb_pow 6 (5/3) (2: ℕ)]
      norm_num
    -- Case x = 81/25
    . have h : x = 81/25 := by assumption
      rw [h]
      rw [← Real.logb_self_eq_one (by norm_num: (1:ℝ) < 6)]
      rw [← Real.logb_div (by norm_num) (by norm_num), ← Real.logb_div (by norm_num) (by norm_num)]
      norm_num
      rw [← abs_two, ← abs_mul, (by norm_num : (2: ℝ) = (2: ℕ)), ← Real.logb_pow 6 (5/3) (2: ℕ)]
      rw [abs_of_nonpos, abs_of_pos, ← Real.logb_inv]
      norm_num
      exact Real.logb_pos (by norm_num: (1:ℝ) < 6) (by norm_num)
      apply le_of_lt
      apply Real.logb_neg (by norm_num: (1:ℝ) < 6) (by norm_num) (by norm_num)