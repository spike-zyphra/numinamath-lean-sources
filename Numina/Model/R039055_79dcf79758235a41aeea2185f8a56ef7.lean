import Mathlib

theorem algebra_187696 (x : ℝ) : (7 : ℝ)^(-x) - 3 * (7^(1 + x)) = 4 ↔ x = -1 := by
  constructor
  · -- First, prove the forward direction: if the equation holds, then x = -1
    intro h
    have h1 : (7 : ℝ) ^ (-x) = 1 / ((7 : ℝ) ^ x) := by
      field_simp [Real.rpow_neg]
      all_goals linarith
    have h2 : (7 : ℝ) ^ (1 + x) = (7 : ℝ) * (7 : ℝ) ^ x := by
      rw [Real.rpow_add]
      ring_nf
      all_goals linarith
    rw [h1, h2] at h
    have h3 : (7 : ℝ) ^ x > 0 := by positivity
    have h4 : 1 - 21 * ((7 : ℝ) ^ x) ^ 2 = 4 * ((7 : ℝ) ^ x) := by
      field_simp at h ⊢
      nlinarith [h, h3, sq_pos_of_pos h3]
    have h5 : 21 * ((7 : ℝ) ^ x) ^ 2 + 4 * ((7 : ℝ) ^ x) - 1 = 0 := by linarith
    have h6 : ((7 : ℝ) ^ x - (1 / 7)) * ((7 : ℝ) ^ x + (1 / 3)) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case $7^x - \frac{1}{7} = 0$
      have h8 : (7 : ℝ) ^ x = (1 / 7 : ℝ) := by linarith
      have h9 : x = -1 := by
        have h10 : (7 : ℝ) ^ (x) = (7 : ℝ) ^ (-1 : ℝ) := by
          rw [h8]
          norm_num
        have h11 : x = -1 := by
          apply_fun (Real.logb (7 : ℝ)) at h10
          have h12 : Real.logb (7 : ℝ) ((7 : ℝ) ^ (x)) = x := by
            rw [Real.logb_rpow]
            all_goals linarith
          have h13 : Real.logb (7 : ℝ) ((7 : ℝ) ^ (-1 : ℝ)) = (-1 : ℝ) := by 
            rw [Real.logb_rpow]
            all_goals linarith
          rw [h12, h13] at h10
          linarith
        exact h11
      exact h9
    · -- Case $7^x + \frac{1}{3} = 0$
      have h9 : (7 : ℝ) ^ x = (-1 / 3 : ℝ) := by linarith
      have h10 : (7 : ℝ) ^ x > 0 := by positivity
      nlinarith
  · -- Now the reverse direction: x = -1 implies the equation
    intro h
    rw [h]
    norm_num [Real.rpow_neg, Real.rpow_add]
    <;> linarith