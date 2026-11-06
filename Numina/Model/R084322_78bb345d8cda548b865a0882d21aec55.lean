import Mathlib

open Real

theorem algebra_296791 {a x : ℝ} (ha : a > x) (hx : x > 1)
    (A B C : ℝ) (hA : A = logb a (logb a x)) (hB : B = (logb a x)^2)
    (hC : C = logb a (x^2)) : C > B ∧ B > A := by

  have h1 : logb a (x ^ 2) = 2 * logb a x := by
      simp [logb_pow]
  rw [h1] at hC
  
  have h2 : logb a x > 0 := by
      apply logb_pos
      all_goals linarith

  have h3 : logb a x < 1 := by
      have h4 : logb a x < logb a a := by
          apply Real.logb_lt_logb
          all_goals linarith
      have h5 : logb a a = 1 := by
          rw [logb_self_eq_one]
          all_goals linarith
      linarith

  have hCB : C > B := by
    rw [hC, hB]
    nlinarith [h2, h3]

  have hA_neg : A < 0 := by
      rw [hA]
      have h6 : logb a x > 0 := h2
      have h7 : logb a x < 1 := h3

      have h8 : logb a (logb a x) = (Real.log (logb a x)) / (Real.log a) := by 
          field_simp [logb]

      have h9 : Real.log (logb a x) < 0 := by
          have h5 : logb a x > 0 := h2
          have h6 : logb a x < 1 := h3
          have h7 : Real.log (logb a x) < Real.log (1 : ℝ) := by 
              apply Real.log_lt_log
              all_goals nlinarith 
          have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
          linarith 
      have h10 : Real.log a > 0 := by
          have h8 : a > 1 := by linarith
          have h9 : Real.log a > Real.log (1 : ℝ) := by 
              apply Real.log_lt_log
              all_goals linarith 
          have h10 : Real.log (1 : ℝ) = 0 := Real.log_one 
          linarith 
      have h11 : (Real.log (logb a x) / Real.log a) < 0 := by 
          apply div_neg_of_neg_of_pos 
          <;> linarith 
      linarith [h8, h9, h10, h11]

  have hB_pos : B > 0 := by 
    rw [hB]
    nlinarith [h2]

  have hBA : B > A := by 
    nlinarith [hA_neg, hB_pos]

  constructor 
  · exact hCB 
  · exact hBA