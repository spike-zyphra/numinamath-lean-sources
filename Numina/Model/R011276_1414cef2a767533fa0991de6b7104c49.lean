import Mathlib

open Real

theorem algebra_612930 {x : ℝ} (hx : 0 < x) :
    (logb 8 (x ^ 3)) ^ 2 - logb 8 (x ^ 3) = 4 ↔
    x = 2 ^ ((1 + √17) / 2) ∨ x = 2 ^ ((1 - √17) / 2) := by 
  constructor
  · -- Assume (logb 8 (x ^ 3)) ^ 2 - logb 8 (x ^ 3) = 4, prove x = 2 ^ ((1 + √17) / 2) ∨ x = 2 ^ ((1 - √17) / 2)
    intro h_eq
    have h1 : (logb 8 (x ^ 3)) ^ 2 - logb 8 (x ^ 3) - 4 = 0 := by linarith
    -- Now, we need to solve this quadratic equation for $\log_8{x^3}$.
    -- The quadratic $y^2 - y - 4 = 0$ has solutions $y = \frac{1 \pm \sqrt{17}}{2}$.
    have h2 : (logb 8 (x ^ 3) - (1 + Real.sqrt 17) / 2) * (logb 8 (x ^ 3) - (1 - Real.sqrt 17) / 2) = 0 := by
      nlinarith [ h1, Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num) ]
    cases (mul_eq_zero.1 h2) with
    | inl h3 =>
      -- $\log_8{x^3} = \frac{1 + \sqrt{17}}{2}$
      have h3' : logb 8 (x ^ 3) = (1 + Real.sqrt 17) / 2 := by linarith
      -- Convert $\log_8{x^3}$ to base 2: $\log_8{x^3} = \log_2{x}$.
      have h4 : logb 8 (x ^ 3) = (logb 2 (x ^ 3)) / (logb 2 (8 : ℝ)) := by 
        field_simp [logb]
      have h5 : logb 2 (8 : ℝ) = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h6 : logb 2 (x ^ 3) = 3 * logb 2 x := by 
        simp [logb_pow]
      have h7 : logb 8 (x ^ 3) = logb 2 x := by
        rw [h4, h5, h6]
        field_simp
      -- So $\log_2{x} = \frac{1 + \sqrt{17}}{2}$.
      have h8 : logb 2 x = (1 + Real.sqrt 17) / 2 := by 
        linarith [h7, h3']
      -- Therefore $x = 2^{\frac{1 + \sqrt{17}}{2}}$.
      have h9 : x = (2 : ℝ) ^ ((1 + Real.sqrt 17) / 2) := by 
        have h10 : x = (2 : ℝ) ^ (logb 2 x) := by 
          field_simp at *
        rw [h10, h8]
      left
      exact h9
    | inr h3 =>
      -- $\log_8{x^3} = \frac{1 - \sqrt{17}}{2}$.
      have h3' : logb 8 (x ^ 3) = (1 - Real.sqrt 17) / 2 := by linarith
      -- Convert $\log_8{x^3}$ to base 2: $\log_8{x^3} = \log_2{x}$.
      have h4 : logb 8 (x ^ 3) = (logb 2 (x ^ 3)) / (logb 2 (8 : ℝ)) := by 
        field_simp [logb]
      have h5 : logb 2 (8 : ℝ) = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h6 : logb 2 (x ^ 3) = 3 * logb 2 x := by 
        simp [logb_pow]
      have h7 : logb 8 (x ^ 3) = logb 2 x := by 
        rw [h4, h5, h6]
        field_simp
      -- So $\log_2{x} = \frac{1 - \sqrt{17}}{2}$.
      have h8 : logb 2 x = (1 - Real.sqrt 17) / 2 := by 
        linarith [h7, h3']
      -- Therefore $x = 2^{\frac{1 - \sqrt{17}}{2}}$.
      have h9 : x = (2 : ℝ) ^ ((1 - Real.sqrt 17) / 2) := by
        have h10 : x = (2 : ℝ) ^ (logb 2 x) := by 
          field_simp at *
        rw [h10, h8]
      right
      exact h9
  · -- Assume x = 2 ^ ((1 + √17) / 2) ∨ x = 2 ^ ((1 - √17) / 2), prove (logb 8 (x ^ 3)) ^ 2 - logb 8 (x ^ 3) = 4
    rintro (h_eq | h_eq)
    · -- Case x = 2 ^ ((1 + √17) / 2)
      have h10 : logb 2 x = (1 + Real.sqrt 17) / 2 := by 
        rw [h_eq]
        have h11 : logb 2 ((2 : ℝ) ^ ((1 + Real.sqrt 17) / 2)) = (1 + Real.sqrt 17) / 2 := by 
          rw [Real.logb_rpow]
          all_goals linarith
        linarith [h11]
      have h11 : logb 8 (x ^ 3) = logb 2 x := by 
        have h4 : logb 8 (x ^ 3) = (logb 2 (x ^ 3)) / (logb 2 (8 : ℝ)) := by 
          field_simp [logb]
        have h5 : logb 2 (8 : ℝ) = 3 := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        have h6 : logb 2 (x ^ 3) = 3 * logb 2 x := by 
          simp [logb_pow]
        rw [h4, h5, h6]
        field_simp
      have h12 : logb 8 (x ^ 3) = (1 + Real.sqrt 17) / 2 := by 
        rw [h11, h10]
      rw [h12]
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num)]
    · -- Case x = 2 ^ ((1 - √17) / 2)
      have h10 : logb 2 x = (1 - Real.sqrt 17) / 2 := by 
        rw [h_eq]
        have h11 : logb 2 ((2 : ℝ) ^ ((1 - Real.sqrt 17) / 2)) = (1 - Real.sqrt 17) / 2 := by
          rw [Real.logb_rpow]
          all_goals linarith
        linarith [h11]
      have h11 : logb 8 (x ^ 3) = logb 2 x := by 
        have h4 : logb 8 (x ^ 3) = (logb 2 (x ^ 3)) / (logb 2 (8 : ℝ)) := by 
          field_simp [logb]
        have h5 : logb 2 (8 : ℝ) = 3 := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        have h6 : logb 2 (x ^ 3) = 3 * logb 2 x := by 
          simp [logb_pow]
        rw [h4, h5, h6]
        field_simp
      have h12 : logb 8 (x ^ 3) = (1 - Real.sqrt 17) / 2 := by 
        rw [h11, h10]
      rw [h12]
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num)]