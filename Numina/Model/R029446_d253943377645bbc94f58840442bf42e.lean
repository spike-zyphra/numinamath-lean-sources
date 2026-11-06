import Mathlib

theorem inequalities_80919 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 16 * (a + b + c) ≥ (1 / a : ℚ) + (1 / b : ℚ) + (1 / c : ℚ)) :
    (1 / (a + b + Real.sqrt (2 * a + 2 * c))) ^ 3 +
    (1 / (b + c + Real.sqrt (2 * b + 2 * a))) ^ 3 +
    (1 / (c + a + Real.sqrt (2 * c + 2 * b))) ^ 3 ≤ 8 / 9 := by 
  have h1 : (a : ℝ) ≥ 1 := by
    exact_mod_cast (show a ≥ 1 by linarith)
  have h2 : (b : ℝ) ≥ 1 := by
    exact_mod_cast (show b ≥ 1 by linarith)
  have h3 : (c : ℝ) ≥ 1 := by
    exact_mod_cast (show c ≥ 1 by linarith)
  have h11 : Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ 2 := by
    have h11 : (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ (4 : ℝ) := by
      nlinarith
    have h112 : Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
    have h114 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h115 : Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ 2 := by
      linarith [h114, h112]
    linarith
  have h12 : (a : ℝ) + (b : ℝ) + Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ (4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 * (a : ℝ) + 2 * (c : ℝ)), Real.sq_sqrt (show 0 ≤ (2 * (a : ℝ) + 2 * (c : ℝ)) by nlinarith), h11
    ]
  have h22 : Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ 2 := by
    have h22 : (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ (4 : ℝ) := by
      nlinarith
    have h222 : Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
    have h224 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h225 : Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ (2 : ℝ) := by
      linarith [h224, h222]
    linarith
  have h23 : (b : ℝ) + (c : ℝ) + Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ (4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 * (b : ℝ) + 2 * (a : ℝ)), Real.sq_sqrt (show 0 ≤ (2 * (b : ℝ) + 2 * (a : ℝ)) by nlinarith), h22
    ]
  have h33 : Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ (2 : ℝ) := by
    have h33 : (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ (4 : ℝ) := by
      nlinarith
    have h332 : Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
    have h334 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h335 : Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ (2 : ℝ) := by
      linarith [h334, h332]
    linarith
  have h34 : (c : ℝ) + (a : ℝ) + Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ (4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 * (c : ℝ) + 2 * (b : ℝ)), Real.sq_sqrt (show 0 ≤ (2 * (c : ℝ) + 2 * (b : ℝ)) by nlinarith), h33
    ]
  have h35 : (1 / (a + b + Real.sqrt (2 * a + 2 * c))) ^ 3 ≤ (1 / 4) ^ 3 := by
    have h101 : (a : ℝ) + (b : ℝ) + Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) ≥ (4 : ℝ) := h12
    have h102 : (a : ℝ) + (b : ℝ) + Real.sqrt (2 * (a : ℝ) + 2 * (c : ℝ)) > 0 := by
      positivity
    have h103 : (1 / (a + b + Real.sqrt (2 * a + 2 * c)) : ℝ) ≤ (1 / 4 : ℝ) := by
      -- We need to show: 1 / (a + b + sqrt(2a + 2c)) ≤ 1 / 4
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith [Real.sqrt_nonneg (2 * (a : ℝ) + 2 * (c : ℝ)), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (a : ℝ) + 2 * (c : ℝ) : ℝ) by positivity), 
                 h11
                 ]
    have h104 : ( (1 / (a + b + Real.sqrt (2 * a + 2 * c)) ) ) ^ 3 ≤ ( ( (1 / 4 : ℝ) ) ) ^ 3 := by
      have h105 : (1 / (a + b + Real.sqrt (2 * a + 2 * c))) ≤ (1 / 4 : ℝ) := h103
      have h106 : (0 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
      have h107 : (1 / (a + b + Real.sqrt (2 * a + 2 * c)) : ℝ) ≥ (0 : ℝ) := by positivity
      -- Apply pow_le_pow_left to preserve the inequality after cubing
      apply pow_le_pow_left
      all_goals
      nlinarith [Real.sqrt_nonneg (2 * (a : ℝ) + 2 * (c : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (a : ℝ) + 2 * (c : ℝ)) by positivity), h11
      ]
      all_goals
      try positivity
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (a : ℝ) + 2 * (c : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (a : ℝ) + 2 * (c : ℝ)) by positivity), h11
      ]
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (a : ℝ) + 2 * (c : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (a : ℝ) + 2 * (c : ℝ)) by positivity), h11
      ]
    simpa using h104
  have h45 : (1 / (b + c + Real.sqrt (2 * b + 2 * a))) ^ 3 ≤ (1 / 4) ^ 3 := by
    have h101 : (b : ℝ) + (c : ℝ) + Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) ≥ (4 : ℝ) := h23
    have h102 : (b : ℝ) + (c : ℝ) + Real.sqrt (2 * (b : ℝ) + 2 * (a : ℝ)) > 0 := by
      positivity
    have h103 : ( (1 / (b + c + Real.sqrt (2 * b + 2 * a)) ) : ℝ ) ≤ ( (1 / 4 : ℝ) ) := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith [Real.sqrt_nonneg (2 * (b : ℝ) + 2 * (a : ℝ)), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (b : ℝ) + 2 * (a : ℝ)) by positivity), 
                 h22
                 ]
    have h104 : ( (1 / (b + c + Real.sqrt (2 * b + 2 * a)) ) : ℝ ) ^ 3 ≤ ( ( (1 / 4 : ℝ) ) ) ^ 3 := by
      have h105 : (1 / (b + c + Real.sqrt (2 * b + 2 * a))) ≤ (1 / 4 : ℝ) := h103
      have h106 : ( (1 / 4 : ℝ) ) ≥ (0 : ℝ) := by norm_num
      have h107 : ( (1 / (b + c + Real.sqrt (2 * b + 2 * a)) ) : ℝ ) ≥ (0 : ℝ) := by positivity
      apply pow_le_pow_left
      all_goals
      nlinarith [Real.sqrt_nonneg (2 * (b : ℝ) + 2 * (a : ℝ)), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (b : ℝ) + 2 * (a : ℝ)) by positivity), 
                 h22
                 ]
      all_goals
      try positivity
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (b : ℝ) + 2 * (a : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (b : ℝ) + 2 * (a : ℝ)) by positivity), h22
      ]
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (b : ℝ) + 2 * (a : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (b : ℝ) + 2 * (a : ℝ)) by positivity), h22
      ]
    simpa using h104
  -- Similarly for the third term:
  have h65 : (1 / (c + a + Real.sqrt (2 * c + 2 * b))) ^ 3 ≤ (1 / 4) ^ 3 := by
    have h101 : (c : ℝ) + (a : ℝ) + Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) ≥ (4 : ℝ) := h34
    have h102 : (c : ℝ) + (a : ℝ) + Real.sqrt (2 * (c : ℝ) + 2 * (b : ℝ)) > 0 := by
      positivity
    have h103 : ( (1 / (c + a + Real.sqrt (2 * c + 2 * b)) : ℝ ) ) ≤ ( (1 / 4 : ℝ) ) := by
      -- We need to show: 1/(c + a + sqrt(2c + 2b)) ≤ 1/4
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      nlinarith [Real.sqrt_nonneg (2 * (c : ℝ) + 2 * (b : ℝ)), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (c : ℝ) + 2 * (b : ℝ)) by positivity), 
                 h33
                 ]
    have h104 : ( (1 / (c + a + Real.sqrt (2 * c + 2 * b)) ) : ℝ ) ^ 3 ≤ ( ( (1 / 4 : ℝ) ) ) ^ 3 := by
      have h105 : ( (1 / (c + a + Real.sqrt (2 * c + 2 * b)) ) : ℝ ) ≤ ( ( (1 / 4 : ℝ) ) ) := h103
      have h106 : ( ( (1 / 4 : ℝ) ) ) ≥ (0 : ℝ) := by norm_num
      have h107 : ( (1 / (c + a + Real.sqrt (2 * c + 2 * b)) : ℝ ) ) ≥ (0 : ℝ) := by positivity
      apply pow_le_pow_left
      all_goals
      nlinarith [Real.sqrt_nonneg (2 * (c : ℝ) + 2 * (b : ℝ)), 
                 Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (c : ℝ) + 2 * (b : ℝ)) by positivity), 
                 h33
                 ]
      all_goals
      try positivity
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (c : ℝ) + 2 * (b : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (c : ℝ) + 2 * (b : ℝ)) by positivity), h33
      ]
      all_goals
      try linarith [Real.sqrt_nonneg (2 * (c : ℝ) + 2 * (b : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (c : ℝ) + 2 * (b : ℝ)) by positivity), h33
      ]
    simpa using h104
  have h75 : (1 / (a + b + Real.sqrt (2 * a + 2 * c)) ) ^ 3 + (1 / (b + c + Real.sqrt (2 * b + 2 * a)) ) ^ 3 + (1 / (c + a + Real.sqrt (2 * c + 2 * b))) ^ 3 ≤ (3 : ℝ) * ( (1 / 4) ^ 3 ) := by
    linarith [h35, h45, h65
    ]
  have h85 : (3 : ℝ) * ( (1 / 4) ^ 3 ) ≤ (8 / 9 : ℝ) := by
    norm_num
  have h95 : (1 / (a + b + Real.sqrt (2 * a + 2 * c)) ) ^ 3 + (1 / (b + c + Real.sqrt (2 * b + 2 * a)) ) ^ 3 + (1 / (c + a + Real.sqrt (2 * c + 2 * b))) ^ 3 ≤ (8 / 9 : ℝ) := by
    linarith [h75, h85
    ]
  exact_mod_cast h95