import Mathlib

theorem algebra_90098
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a ^ b = 343)
    (h2 : b ^ c = 10)
    (h3 : a ^ c = 7) :
    b ^ b = 1000 := by
  have h1' : b * (Real.log a) = Real.log 343 := by 
    calc
      b * (Real.log a) = (Real.log (a ^ b)) := by 
        rw [Real.log_rpow]
        all_goals linarith
      _ = Real.log 343 := by 
        rw [h1]
        all_goals linarith
  have h2' : c * (Real.log b) = Real.log 10 := by 
    calc
      c * (Real.log b) = (Real.log (b ^ c)) := by 
        rw [Real.log_rpow]
        all_goals linarith
      _ = Real.log 10 := by 
        rw [h2]
        all_goals linarith
  have h3' : c * (Real.log a) = Real.log 7 := by 
    calc
      c * (Real.log a) = (Real.log (a ^ c)) := by 
        rw [Real.log_rpow]
        all_goals linarith
      _ = Real.log 7 := by 
        rw [h3]
        all_goals linarith
  have h4 : Real.log 343 = 3 * Real.log 7 := by
    calc
      Real.log 343 = Real.log (7 ^ 3) := by norm_num
      _ = 3 * Real.log 7 := by 
        simp [Real.log_pow]
        <;> linarith
  have h1'' : b * (Real.log a) = 3 * Real.log 7 := by 
    linarith [h1', h4]
  have h5 : Real.log 7 ≠ 0 := by
    have h6 : Real.log 7 > 0 := by
      apply Real.log_pos
      all_goals linarith
    linarith
  have h7 : b = 3 * c := by
    have eq1 : b * (Real.log a) = 3 * Real.log 7 := h1''
    have eq2 : c * (Real.log a) = Real.log 7 := h3'
    have h7 : b = 3 * c := by 
      apply (mul_left_inj' h5).mp
      nlinarith
      all_goals linarith 
    assumption
  -- Now that we have b=3c, so we need to compute b^b
  have h8 : b ^ b = 1000 := by
    have h9 : b = 3 * c := h7
    have h10 : b ^ c = 10 := by linarith [h2]
    have h11 : b / c = 3 := by
      rw [show b = 3 * c by linarith [h9]]
      field_simp [hc.ne.symm]
      <;> linarith
    -- calculated the required values, now need to establish b^b=1000
    calc
      b ^ b = (b ^ c) ^ (b / c) := by 
        rw [← Real.rpow_mul]
        field_simp
        all_goals try positivity
        all_goals try linarith
      _ = (10:ℝ) ^ (3:ℝ) := by 
        rw [show b ^ c = (10:ℝ) by linarith [h10]]
        rw [show b / c = (3:ℝ) by linarith [h11]]
      _ = (1000:ℝ) := by norm_num
    all_goals try linarith
  linarith [h8]
  all_goals try linarith
  all_goals try positivity