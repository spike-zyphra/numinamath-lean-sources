import Mathlib

theorem inequalities_224686 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a > b) :
    a^a * b^b > a^b * b^a := by
  have h1 : a > b := hab
  have h2 : 0 < b := hb
  have h3 : 0 < a := ha
  have h4 : a ^ a * b ^ b = Real.exp (a * (Real.log a) + b * (Real.log b)) := by
    have h5 : (a ^ a * b ^ b) = Real.exp (a * (Real.log a) + b * (Real.log b)) := by
      have h6 : Real.log (a ^ a * b ^ b) = a * (Real.log a) + b * (Real.log b) := by
        calc
          Real.log (a ^ a * b ^ b) = Real.log (a ^ a) + Real.log (b ^ b) := by
            rw [Real.log_mul (by positivity) (by positivity)]
          _ = a * Real.log a + b * Real.log b := by
            rw [Real.log_rpow, Real.log_rpow]
            all_goals
              linarith
          _ = a * (Real.log a) + b * (Real.log b) := by ring
      have h7 : a ^ a * b ^ b = Real.exp (Real.log (a ^ a * b ^ b)) := by
        rw [Real.exp_log]
        positivity
      rw [h7]
      rw [h6]
    linarith [h5]
  have h8 : a ^ b * b ^ a = Real.exp (b * (Real.log a) + a * (Real.log b)) := by
    have h9 : (a ^ b * b ^ a) = Real.exp (b * (Real.log a) + a * (Real.log b)) := by
      have h10 : Real.log (a ^ b * b ^ a) = b * (Real.log a) + a * (Real.log b) := by
        calc
          Real.log (a ^ b * b ^ a) = Real.log (a ^ b) + Real.log (b ^ a) := by
            rw [Real.log_mul (by positivity) (by positivity)]
          _ = b * Real.log a + a * Real.log b := by
            rw [Real.log_rpow, Real.log_rpow]
            all_goals
              linarith
          _ = b * (Real.log a) + a * (Real.log b) := by ring
      have h11 : a ^ b * b ^ a = Real.exp (Real.log (a ^ b * b ^ a)) := by
        rw [Real.exp_log]
        positivity
      rw [h11]
      rw [h10]
    linarith [h9]
  have h12 : a * Real.log a + b * Real.log b > b * Real.log a + a * Real.log b := by
    have h13 : a - b > 0 := by linarith
    have h14 : Real.log a - Real.log b > 0 := by
      have h15 : a > b := by linarith
      have h16 : Real.log a > Real.log b := by
        apply Real.log_lt_log
        all_goals linarith
      linarith [h16]
    have h17 : (a - b) * (Real.log a - Real.log b) > 0 := by
      exact mul_pos h13 h14
    linarith [h17]
  have h18 : Real.exp (a * Real.log a + b * Real.log b) > Real.exp (b * Real.log a + a * Real.log b) := by
    apply Real.exp_strictMono
    linarith [h12]
  rw [h4, h8]
  all_goals
    linarith [h18]