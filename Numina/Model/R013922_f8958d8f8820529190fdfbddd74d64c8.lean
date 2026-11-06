import Mathlib

open Real

theorem inequalities_112228 {a b : ℝ} (ha : a > 1) (hb : b > 0) :
    logb a (a^b - 1) * logb a (a^b + 1) < b^2 := by

  have h1 : a ^ b > 1 := by
    have h2 : a ^ b > (1 : ℝ) := by
      have h3 : a > 1 := by linarith
      have h4 : b > 0 := by linarith
      apply Real.one_lt_rpow
      all_goals linarith
    linarith

  have h2 : a ^ b - 1 > 0 := by
    linarith

  have h3 : a ^ b + 1 > 0 := by
    linarith

  have h4 : logb a (a^b - 1) = logb a (a ^ b) + logb a (1 - 1 / a ^ b) := by
    have h5 : a ^ b - 1 = (a ^ b) * (1 - 1 / a ^ b) := by
      field_simp
      <;> nlinarith
    rw [h5]
    have h6 : logb a ((a ^ b) * (1 - 1 / a ^ b)) = logb a (a ^ b) + logb a (1 - 1 / a ^ b) := by
      rw [logb_mul (by positivity) (by
        have h5 : (1 - 1 / a ^ b : ℝ) > 0 := by
          have h10 : a ^ b > 1 := by linarith
          have h11 : 1 / a ^ b < 1 := by
            apply (div_lt_iff₀ (by positivity)).mpr
            nlinarith
          nlinarith
        linarith
      )]
    linarith

  have h5 : logb a (a^b + 1) = logb a (a ^ b) + logb a (1 + 1 / a ^ b) := by
    have h6 : a ^ b + 1 = (a ^ b) * (1 + 1 / a ^ b) := by
      field_simp
      <;> nlinarith
    rw [h6]
    have h7 : logb a ((a ^ b) * (1 + 1 / a ^ b)) = logb a (a ^ b) + logb a (1 + 1 / a ^ b) := by
      rw [logb_mul (by positivity) (by
        have h8 : (1 + 1 / a ^ b : ℝ) > 0 := by
          have h9 : a ^ b > 0 := by positivity
          have h10 : 1 / a ^ b > 0 := by positivity
          nlinarith
        linarith
      )]
    linarith

  have h6 : logb a (a ^ b) = b := by
    rw [logb_rpow (by linarith) (by linarith)]

  rw [h4, h5, h6]

  have h7 : (1 - 1 / a ^ b : ℝ) > 0 := by
    have h10 : a ^ b > 1 := by linarith
    have h11 : 1 / a ^ b < 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    nlinarith

  have h8 : (1 + 1 / a ^ b : ℝ) > 1 := by
    have h9 : a ^ b > 0 := by positivity
    have h10 : 1 / a ^ b > 0 := by positivity
    nlinarith

  have h9 : logb a (1 - 1 / a ^ b) < 0 := by
    have h10 : (1 - 1 / a ^ b : ℝ) > 0 := h7
    have h11 : (1 - 1 / a ^ b : ℝ) < 1 := by
      have h10 : a ^ b > 1 := by linarith
      have h11 : 1 / a ^ b > 0 := by positivity
      nlinarith
    have h12 : logb a (1 - 1 / a ^ b) < logb a (1 : ℝ) := by
      apply logb_lt_logb
      all_goals
        try linarith
        try nlinarith
    have h13 : logb a (1 : ℝ) = 0 := by
      simp [logb_one]
    nlinarith

  have h10 : logb a (1 + 1 / a ^ b) > 0 := by
    have h11 : (1 + 1 / a ^ b : ℝ) > 1 := h8
    have h12 : logb a (1 + 1 / a ^ b) > logb a (1 : ℝ) := by
      apply logb_lt_logb
      all_goals
        try linarith
        try nlinarith
    have h13 : logb a (1 : ℝ) = 0 := by
      simp [logb_one]
    nlinarith

  have h11 : logb a (1 - 1 / a ^ b) * logb a (1 + 1 / a ^ b) < 0 := by
    have h12 : logb a (1 - 1 / a ^ b) < 0 := h9
    have h13 : logb a (1 + 1 / a ^ b) > 0 := h10
    nlinarith

  have h12 : logb a (1 - 1 / a ^ b) + logb a (1 + 1 / a ^ b) < 0 := by
    have h13 : logb a (1 - 1 / a ^ b) + logb a (1 + 1 / a ^ b) = logb a ((1 - 1 / a ^ b) * (1 + 1 / a ^ b)) := by
      rw [← logb_mul (by positivity) (by positivity)]
    rw [h13]
    have h14 : (1 - 1 / a ^ b : ℝ) * (1 + 1 / a ^ b : ℝ) = 1 - 1 / a^(2 * b) := by
      have h15 : (1 - 1 / a ^ b : ℝ) * (1 + 1 / a ^ b : ℝ) = 1 - (1 / a ^ b) ^ 2 := by
        ring
      rw [h15]
      have h16 : (1 / a ^ b : ℝ) ^ 2 = 1 / a^(2 * b) := by
        have h17 : a ^ (2 * b) = (a ^ b) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
        field_simp [h17]
      rw [h16]

    rw [h14]
    have h15 : a ^ (2 * b) > 1 := by
      have h16 : a ^ b > 1 := by
        have h3 : a > 1 := by linarith
        have h4 : b > 0 := by linarith
        apply Real.one_lt_rpow
        all_goals linarith
      have h17 : a ^ (2 * b) = (a ^ b) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals linarith
      rw [h17]
      nlinarith

    have h17 : (1 - 1 / a^(2 * b) : ℝ) < 1 := by
      have h18 : a ^ (2 * b) > 1 := h15
      have h19 : 1 / a ^ (2 * b) > 0 := by positivity
      nlinarith

    have h18 : logb a (1 - 1 / a ^ (2 * b)) < 0 := by
      have h19 : logb a (1 - 1 / a ^ (2 * b)) < logb a (1 : ℝ) := by
        apply logb_lt_logb
        all_goals
          try linarith
          try nlinarith
      have h20 : logb a (1 : ℝ) = 0 := by
        simp [logb_one]
      nlinarith

    linarith

  nlinarith [mul_pos (show 0 < b by linarith) (show 0 < (1 : ℝ) by linarith), mul_pos (show 0 < (1 : ℝ) by linarith) (show 0 < (1 : ℝ) by linarith)]