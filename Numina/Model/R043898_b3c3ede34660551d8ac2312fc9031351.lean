import Mathlib

open Real

theorem inequalities_171273 (x : ℝ) (hx : 0 < x) :
    5 ^ (logb 5 x) ^ 2 + x ^ (logb 5 x) < 10 ↔ x ∈ Set.Ioo (1 / 5) 5 := by
  constructor
  · -- Forward direction: if inequality $5^{\log_{5}^{2} x} + x^{\log_{5} x} < 10$ holds, then $x \in (\frac{1}{5}, 5)$
    intro h
    have h1 : (5 : ℝ) ^ (logb 5 x) ^ 2 = (5 ^ (logb 5 x)) ^ (logb 5 x) := by
      calc
        (5 : ℝ) ^ (logb 5 x) ^ 2 = (5 : ℝ) ^ (logb 5 x * logb 5 x) := by ring_nf
        _ = ((5 : ℝ) ^ (logb 5 x)) ^ (logb 5 x) := by rw [← Real.rpow_mul]; ring_nf; all_goals linarith
    have h2 : (5 : ℝ) ^ (logb 5 x) ^ 2 = x ^ (logb 5 x) := by
      rw [h1]
      have h3 : (5 : ℝ) ^ (logb 5 x) = x := by
        rw [Real.rpow_logb]
        all_goals
          try linarith
          try { tauto }
          try { positivity }
      rw [h3]
      <;> nlinarith
    have h4 : (5 : ℝ) ^ (logb 5 x) ^ 2 + x ^ (logb 5 x) = 2 * (x ^ (logb 5 x)) := by
      rw [h2]
      ring
    have h5 : x ^ (logb 5 x) < 5 := by
      nlinarith [h4, h]
    have h6 : logb 5 (x ^ (logb 5 x)) = logb 5 x * logb 5 x := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals
        linarith
    have h7 : logb 5 (5 : ℝ) = 1 := by
      rw [logb_self_eq_one]
      all_goals
        try linarith
        try { tauto }
        try { positivity }
    have h8 : logb 5 (x ^ (logb 5 x)) < logb 5 (5 : ℝ) := by
      have h9 : x ^ (logb 5 x) < (5 : ℝ) := by linarith
      have h10 : logb 5 (x ^ (logb 5 x)) < logb 5 (5 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals
          try linarith
          try { tauto }
          try { positivity }
      linarith
    have h11 : (logb 5 x) ^ 2 < 1 := by
      have h12 : logb 5 (x ^ (logb 5 x)) = (logb 5 x) ^ 2 := by
        nlinarith [h6]
      nlinarith [h12, h8, h7]
    have h12 : -1 < logb 5 x := by
      nlinarith
    have h13 : logb 5 x < 1 := by
      nlinarith
    have h14 : x > (1 / 5 : ℝ) := by
      by_contra h
      push_neg at h
      have h15 : logb 5 x ≤ -1 := by
        have h16 : x ≤ (1 / 5 : ℝ) := by linarith
        have h17 : logb 5 x ≤ logb 5 (1 / 5 : ℝ) := by
          apply logb_le_logb_of_le
          all_goals
            try linarith
            try { tauto }
            try { positivity }
        have h18 : logb 5 (1 / 5 : ℝ) = -1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
          <;> linarith
        nlinarith [h17, h18]
      nlinarith
    have h15 : x < (5 : ℝ) := by
      by_contra h
      push_neg at h
      have h16 : logb 5 x ≥ 1 := by
        have h17 : x ≥ (5 : ℝ) := by linarith
        have h18 : logb 5 x ≥ logb 5 (5 : ℝ) := by
          apply logb_le_logb_of_le
          all_goals
            try linarith
            try { tauto }
            try { positivity }
        have h19 : logb 5 (5 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals
            try linarith
            try { tauto }
            try { positivity }
        nlinarith [h18, h19]
      nlinarith
    exact ⟨by linarith, by linarith⟩
  · -- Backward direction: if $x \in (\frac{1}{5}, 5)$, then $5^{\log_{5}^{2} x} + x^{\log_{5} x} < 10$
    rintro ⟨hx1, hx2⟩
    have h1 : (5 : ℝ) ^ (logb 5 x) ^ 2 = (5 ^ (logb 5 x)) ^ (logb 5 x) := by
      calc
        (5 : ℝ) ^ (logb 5 x) ^ 2 = (5 : ℝ) ^ (logb 5 x * logb 5 x) := by ring_nf
        _ = ((5 : ℝ) ^ (logb 5 x)) ^ (logb 5 x) := by rw [← Real.rpow_mul]; ring_nf; all_goals linarith
    have h2 : (5 : ℝ) ^ (logb 5 x) ^ 2 = x ^ (logb 5 x) := by
      rw [h1]
      have h3 : (5 : ℝ) ^ (logb 5 x) = x := by
        rw [Real.rpow_logb]
        all_goals
          try linarith
          try { tauto }
          try { positivity }
      rw [h3]
      <;> nlinarith
    have h4 : (5 : ℝ) ^ (logb 5 x) ^ 2 + x ^ (logb 5 x) = 2 * (x ^ (logb 5 x)) := by
      rw [h2]
      ring
    have h5 : x ^ (logb 5 x) < (5 : ℝ) := by
      -- Proof that x^(logb 5 x) < 5
      have h11 : -1 < logb 5 x := by
        have h12 : x > (1 / 5 : ℝ) := hx1
        have h13 : logb 5 x > -1 := by
          have h21 : logb 5 (1 / 5 : ℝ) = -1 := by
            rw [logb_eq_iff_rpow_eq] <;> norm_num
            <;> linarith
          have h22 : logb 5 x > logb 5 (1 / 5 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals
              try linarith
              try { tauto }
              try { positivity }
          nlinarith [h21, h22]
        linarith
      have h12 : logb 5 x < (1 : ℝ) := by
        have h13 : x < (5 : ℝ) := hx2
        have h14 : logb 5 x < (1 : ℝ) := by
          have h21 : logb 5 (5 : ℝ) = (1 : ℝ) := by
            rw [logb_self_eq_one]
            all_goals linarith
          have h22 : logb 5 x < logb 5 (5 : ℝ) := by
            apply Real.logb_lt_logb
            all_goals
              try linarith
              try { tauto }
              try { positivity }
          nlinarith [h21, h22]
        linarith
      have h8 : (logb 5 x) ^ 2 < (1 : ℝ) := by
        nlinarith 
      -- From h8: (logb 5 x) ^ 2 < 1, we need to show x ^ (logb 5 x) < 5
      have h16 : logb 5 (x ^ (logb 5 x)) < logb 5 (5 : ℝ) := by
        have h17 : logb 5 (x ^ (logb 5 x)) = (logb 5 x) ^ 2 := by 
          rw [logb_rpow_eq_mul_logb_of_pos] 
          all_goals nlinarith
        have h18 : (logb 5 x) ^ 2 < (1 : ℝ) := h8 
        have h19 : logb 5 (5 : ℝ) = (1 : ℝ) := by
          rw [logb_self_eq_one]
          all_goals nlinarith
        nlinarith [h17, h18, h19]
      have h20 : x ^ (logb 5 x) < (5 : ℝ) := by
        have h21 : x ^ (logb 5 x) > 0 := by positivity
        have h22 : (5 : ℝ) > (0 : ℝ) := by norm_num
        have h23 : (5 : ℝ) > (1 : ℝ) := by norm_num
        -- Now, from h16 we can derive our goal
        have h24 : logb 5 (x ^ (logb 5 x)) < logb 5 (5 : ℝ) := h16
        -- Use strict increasing of logarithm 
        have h25 : x ^ (logb 5 x) < (5 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by positivity) (by linarith)).mp at h24
          linarith 
        linarith 
      exact h20 
    nlinarith [h4, h5]