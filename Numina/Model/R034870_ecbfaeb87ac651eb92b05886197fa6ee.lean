import Mathlib

theorem algebra_310740 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a^b = b^a) (h2 : b = 9 * a) :
    a = 3 ^ ((1 : ℝ) / 4) := by
  rw [show b = 9 * a by linarith [h2]] at h1
  have h3 : a ^ (9 * a) = (9 * a) ^ a := by
    simpa using h1
  -- Take natural logarithm on both sides of $a^{9a} = (9a)^a$
  have h4 : 9 * a * (Real.log a) = a * (Real.log (9 * a)) := by
    have h5 : Real.log (a ^ (9 * a)) = Real.log ((9 * a) ^ a) := by
      rw [h3]
    have h6 : Real.log (a ^ (9 * a)) = 9 * a * Real.log a := by 
      rw [Real.log_rpow]
      all_goals nlinarith
    have h7 : Real.log ((9 * a) ^ a) = a * Real.log (9 * a) := by 
      rw [Real.log_rpow]
      all_goals
      nlinarith
    rw [h6, h7] at h5
    linarith
  -- from h4, since a > 0, so we have 9 * log a = log (9 * a)
  have h6 : 9 * Real.log a = Real.log (9 * a) := by
    have h8 : a > 0 := by assumption
    apply (mul_left_inj' (show a ≠ 0 by linarith)).mp
    linarith [h4]
  
  -- Expanding the right side: $\ln(9a) = \ln(9) + \ln(a)$
  have h7 : Real.log (9 * a) = Real.log (9) + Real.log a := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  
  -- Substituting h7 into h6: $9 \ln(a) = \ln(9) + \ln(a)$
  rw [h7] at h6
  
  -- Solving gives $\ln(a) = \ln(9)/8$
  have h8 : Real.log a = Real.log (9) / 8 := by
    linarith
  
  -- Since $9 = 3^2$, $\ln(9) = 2 \ln(3)$
  have h9 : Real.log (9 : ℝ) = 2 * Real.log (3) := by
    have h9 : Real.log (9 : ℝ) = Real.log (3 ^ 2) := by
      norm_num
    rw [h9]
    simp [Real.log_pow]
    all_goals linarith
  
  -- Substituting $\ln(9) = 2 \ln(3)$ into $\ln(a) = \ln(9)/8$
  rw [h9] at h8
  -- $\ln(a) = \ln(3)/4$
  have h8' : Real.log a = Real.log (3) / 4 := by
    linarith
  
  -- convert to $a = 3^{1/4}$
  have h9 : a = (3 : ℝ) ^ ((1 : ℝ) / 4) := by
    -- $a = e^{\ln(a)}$, and $\ln(a) = \ln(3)/4$.
    -- So $a = e^{\ln(3)/4} = (e^{\ln(3)})^{1/4} = 3^{1/4}$
    have h10 : Real.log a = Real.log (3 ^ ((1 : ℝ) / 4)) := by
      rw [h8']
      have h11 : Real.log (3 ^ ((1 : ℝ) / 4)) = Real.log (3) * (1 / 4) := by 
        rw [Real.log_rpow]
        all_goals linarith
      rw [h11]
      all_goals ring_nf <;> linarith
    have h12 : a > 0 := by assumption
    have h13 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
    have h14 : a = (3 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h12) (Set.mem_Ioi.mpr h13) h10
      all_goals linarith
    exact h14
  
  exact h9