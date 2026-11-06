import Mathlib

theorem inequalities_596990 (a : ℝ) (ha : 0 < a ∧ a < 1) :
    a^a > a^(a^a) ∧ a^(a^a) > a := by
  have h1 : 0 < a := ha.1
  have h2 : a < 1 := ha.2

  have h3 : a ^ a < 1 := by
    have h4 : Real.log (a ^ a) < 0 := by
      have h5 : Real.log (a ^ a) = a * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          try linarith
      rw [h5]
      have h6 : Real.log a < 0 := by
        have h7 : Real.log a < Real.log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h9 : a > 0 := by linarith
      nlinarith
    have h10 : a ^ a < 1 := by
      by_contra h
      push_neg at h
      have h11 : Real.log (a ^ a) ≥ Real.log (1 : ℝ) := by
        apply Real.log_le_log
        · 
          have h13 : a ^ a > 0 := by positivity
          linarith
        · linarith
      have h14 : Real.log (1 : ℝ) = 0 := Real.log_one
      linarith [h4, h14]
    linarith

  have h11 : a ^ (a ^ a) > a := by
    have h12 : Real.log (a ^ (a ^ a)) > Real.log (a) := by
      have h13 : Real.log (a ^ (a ^ a)) = a ^ a * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          try positivity
          try linarith
      rw [h13]
      have h14 : Real.log a < 0 := by
        have h7 : Real.log a < Real.log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h15 : a ^ a > 0 := by positivity
      have h16 : a ^ a < 1 := h3
      nlinarith
    have h17 : a ^ (a ^ a) > a := by
      by_contra h
      push_neg at h
      have h18 : Real.log (a ^ (a ^ a)) ≤ Real.log (a) := by
        apply Real.log_le_log
        · 
          have h10 : a ^ (a ^ a) > 0 := by positivity
          linarith
        · linarith
      linarith
    linarith

  have h18 : a ^ a > a ^ (a ^ a) := by
    have h19 : Real.log (a ^ a) > Real.log (a ^ (a ^ a)) := by
      have h20 : Real.log (a ^ a) = a * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          try linarith
      have h21 : Real.log (a ^ (a ^ a)) = a ^ a * Real.log a := by
        rw [Real.log_rpow]
        all_goals
          try positivity
          try linarith
      rw [h20, h21]
      have h22 : Real.log a < 0 := by
        have h7 : Real.log a < Real.log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
        linarith
      have h23 : a ^ a > 0 := by positivity
      have h24 : a < a ^ a := by
        have h28 : Real.log a < Real.log (a ^ a) := by
          have h29 : Real.log (a ^ a) = a * Real.log a := by
            rw [Real.log_rpow]
            all_goals
              try linarith
          have h30 : Real.log a < a * Real.log a := by
            have h31 : Real.log a < 0 := by
              have h7 : Real.log a < Real.log (1 : ℝ) := by
                apply Real.log_lt_log
                all_goals
                  try linarith
              have h8 : Real.log (1 : ℝ) = 0 := Real.log_one
              linarith
            have h32 : 1 - a > 0 := by linarith
            nlinarith
          nlinarith
        have h33 : a > 0 := by linarith
        have h34 : a ^ a > 0 := by positivity
        apply (Real.log_lt_log_iff (by linarith) (by positivity)).mp at h28
        all_goals linarith
      nlinarith
    have h28 : a ^ a > a ^ (a ^ a) := by
      by_contra h
      push_neg at h
      have h29 : Real.log (a ^ a) ≤ Real.log (a ^ (a ^ a)) := by
        apply Real.log_le_log
        · 
          have h10 : a ^ a > 0 := by positivity
          linarith
        · 
          have h111 : a ^ (a ^ a) > 0 := by positivity
          linarith
      linarith
    linarith

  constructor
  · exact h18
  · exact h11