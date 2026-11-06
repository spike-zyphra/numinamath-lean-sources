import Mathlib


lemma lemma_1 {a : ℝ} (ha : 0 < a ∧ a < 1) :
    a ^ a > a ^ (a ^ a) := by
  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2
  have h3 : a ^ a > a := by
    have h4 : a < 1 := h2
    have h5 : a ^ a > a := by
      have h6 : a ^ a = Real.exp (a * Real.log a) := by
        rw [Real.rpow_def_of_pos h1]
        field_simp [Real.log_exp]
        all_goals try linarith
      have h7 : Real.exp (a * Real.log a) > a := by
        have h8 : Real.log a < 0 := by
          have h9 : a < 1 := by linarith
          have h10 : Real.log a < 0 := by
            have h11 : Real.log a < Real.log (1 : ℝ) := by
              apply Real.log_lt_log
              all_goals linarith
            have h12 : Real.log (1 : ℝ) = 0 := Real.log_one
            nlinarith
          linarith
        have h10 : a * Real.log a > Real.log a := by
          nlinarith
        have h11 : Real.exp (a * Real.log a) > Real.exp (Real.log a) := by
          apply Real.exp_strictMono
          all_goals nlinarith
        have h12 : Real.exp (Real.log a) = a := by
          rw [Real.exp_log]
          all_goals linarith
        nlinarith
      have h8 : a ^ a = Real.exp (a * Real.log a) := h6
      linarith
    linarith
  have h7 : a ^ a > a ^ (a ^ a) := by
    apply Real.rpow_lt_rpow_of_exponent_gt
    all_goals
      try linarith [show 0 < a by linarith, h3, show 0 < a ^ a by positivity]
  linarith


theorem algebra_176250 (a b c : ℝ) (ha : a = Real.exp (-2)) (hb : b = a^(a)) (hc : c = a^(a^(a))) :
    b > a ∧ b > c := by
  have ha01 : 0 < a := by 
    rw [ha]
    positivity
  have ha02 : a < 1 := by 
    rw [ha]
    have h1 : Real.exp (-2 : ℝ) < Real.exp (0 : ℝ) := by
      apply Real.exp_strictMono
      all_goals linarith
    have h6 : Real.exp (0 : ℝ) = 1 := by
      simp
    have h5 : Real.exp (-2 : ℝ) < 1 := by
      linarith
    linarith
  have hb05 : b > a := by 
    rw [hb]
    have h3 : a ^ a > a := by
      have ha : 0 < a ∧ a < 1 := ⟨by linarith, by linarith⟩
      have h4 : a ^ a > a := by
        have h6 : a ^ a = Real.exp (a * Real.log a) := by
          rw [Real.rpow_def_of_pos (by linarith)]
          field_simp [Real.log_exp]
          all_goals try linarith
        have h7 : Real.exp (a * Real.log a) > a := by
          have h8 : Real.log a < 0 := by
            have h9 : a < 1 := by linarith
            have h10 : Real.log a < 0 := by
              have h11 : Real.log a < Real.log (1 : ℝ) := by
                apply Real.log_lt_log
                all_goals linarith
              have h12 : Real.log (1 : ℝ) = 0 := Real.log_one
              nlinarith
            linarith
          have h10 : a * Real.log a > Real.log a := by
            nlinarith
          have h11 : Real.exp (a * Real.log a) > Real.exp (Real.log a) := by
            apply Real.exp_strictMono
            all_goals nlinarith
          have h12 : Real.exp (Real.log a) = a := by
            rw [Real.exp_log]
            all_goals linarith
          nlinarith
        have h6 : a ^ a = Real.exp (a * Real.log a) := h6
        linarith
      linarith
    have hb03 : 0 < a ^ a := by
      positivity
    have hb04 : a ^ a > a := h3
    linarith
  have hb04 : b > c := by
    rw [hc]
    have h4 : a ^ a > a ^ (a ^ a) := by
      have ha : 0 < a ∧ a < 1 := ⟨by linarith, by linarith⟩
      apply lemma_1
      all_goals 
        try tauto
    have hb03 : b = a ^ a := by 
      linarith [hb]
    have hb03' : c = a ^ (a ^ a) := by 
      linarith [hc]
    nlinarith
  constructor 
  · linarith [hb05]
  · linarith [hb04]