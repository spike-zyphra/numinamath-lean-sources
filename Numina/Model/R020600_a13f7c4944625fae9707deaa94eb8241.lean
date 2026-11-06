import Mathlib

theorem calculus_81720 (f : ℝ → ℝ) (hf : f = fun x => x ^ 4 + 2 * x ^ 3 - 11 * x ^ 2 - 13 * x + 35)
    (x1 x2 : ℝ) (hx1 : f x1 = -x1 - 1) (hx2 : f x2 = -x2 - 1) (hxy : x1 ≠ x2) :
    deriv f x1 = -1 ∧ deriv f x2 = -1 := by

  have eq1 : x1 ^ 4 + 2 * x1 ^ 3 - 11 * x1 ^ 2 - 13 * x1 + 35 = -x1 - 1 := by 
    rw [hf] at hx1
    simpa using hx1

  have eq2 : x2 ^ 4 + 2 * x2 ^ 3 - 11 * x2 ^ 2 - 13 * x2 + 35 = -x2 - 1 := by 
    rw [hf] at hx2
    simpa using hx2

  have eq3 : x1 ^ 4 + 2 * x1 ^ 3 - 11 * x1 ^ 2 - 12 * x1 + 36 = 0 := by 
    nlinarith 
  have eq4 : x2 ^ 4 + 2 * x2 ^ 3 - 11 * x2 ^ 2 - 12 * x2 + 36 = 0 := by 
    nlinarith 
  have eq5 : (x1 - 2) ^ 2 * (x1 + 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x1 - 2), sq_nonneg (x1 + 3), sq_nonneg (x1 ^ 2 - x1 * 2), sq_nonneg (x1 ^ 2 + (x1 * 6)), sq_pos_of_ne_zero (sub_ne_zero_of_ne hxy)]
  have eq6 : (x2 - 2) ^ 2 * (x2 + 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x2 - 2), sq_nonneg (x2 + 3), sq_nonneg (x2 ^ 2 - x2 * 2), sq_nonneg (x2 ^ 2 + (x2 * 6)), sq_pos_of_ne_zero (sub_ne_zero_of_ne hxy)]

  have h1 : x1 = 2 ∨ x1 = -3 := by
    cases (mul_eq_zero.mp eq5) with
    | inl h2 =>
      have : x1 - 2 = 0 := by
        apply pow_eq_zero 
        exact h2 
      left 
      linarith 
    | inr h2 =>
      have : x1 + 3 = 0 := by
        apply pow_eq_zero 
        exact h2 
      right 
      linarith 

  have h2 : x2 = 2 ∨ x2 = -3 := by
    cases (mul_eq_zero.mp eq6) with
    | inl h2 =>
      have : x2 - 2 = 0 := by
        apply pow_eq_zero 
        exact h2 
      left 
      linarith 
    | inr h2 =>
      have : x2 + 3 = 0 := by
        apply pow_eq_zero 
        exact h2 
      right 
      linarith 
  cases h1 with 
  | inl h1 =>
    cases h2 with 
    | inl h2 =>
      exfalso 
      apply hxy 
      all_goals 
      linarith 
    | inr h2 =>
      constructor 
      · -- Show deriv f x1 = -1 
        rw [hf] 
        simp [deriv_pow, deriv_add, deriv_sub, deriv_const, mul_comm] 
        rw [show x1 = (2 : ℝ) by linarith [h1] ] 
        norm_num 
      · -- Show deriv f x2 = -1 
        rw [hf] 
        simp [deriv_pow, deriv_add, deriv_sub, deriv_const, mul_comm] 
        rw [show x2 = (-3 : ℝ) by linarith [h2] ] 
        norm_num 
  | inr h1 =>
    cases h2 with 
    | inl h2 =>
      constructor 
      · -- Show deriv f x1 = -1 
        rw [hf] 
        simp [deriv_pow, deriv_add, deriv_sub, deriv_const, mul_comm] 
        rw [show x1 = (-3 : ℝ) by linarith [h1] ] 
        norm_num 
      · -- Show deriv f x2 = -1 
        rw [hf] 
        simp [deriv_pow, deriv_add, deriv_sub, deriv_const, mul_comm] 
        rw [show x2 = (2 : ℝ) by linarith [h2] ] 
        norm_num 
    | inr h2 =>
      exfalso 
      apply hxy 
      all_goals 
      linarith