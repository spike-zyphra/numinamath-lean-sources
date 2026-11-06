import Mathlib

theorem algebra_147667 {a b c : ℝ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : (a ^ 2 * b) ^ Real.logb a c = a * (a * c) ^ Real.logb a b) :
    Real.logb c (a * b) = 2 := by

  have h1 : Real.logb a ((a ^ 2 * b) ^ Real.logb a c) = Real.logb a (a * (a * c) ^ Real.logb a b) := by 
    rw [h]

  have eq2 : Real.logb a ((a ^ 2 * b) ^ Real.logb a c) = Real.logb a c * Real.logb a (a ^ 2 * b) := by 
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    all_goals 
      try positivity

  have eq3 : Real.logb a (a * (a * c) ^ Real.logb a b) = 1 + Real.logb a b * Real.logb a (a * c) := by 
    have h4 : Real.logb a (a * (a * c) ^ Real.logb a b) = Real.logb a a + Real.logb a ((a * c) ^ Real.logb a b) := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    have h5 : Real.logb a a = 1 := by 
      rw [Real.logb_self_eq_one]
      all_goals linarith
    have h6 : Real.logb a ((a * c) ^ Real.logb a b) = Real.logb a b * Real.logb a (a * c) := by 
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals 
        try positivity 
    rw [h4, h5, h6]

  have eq7 : Real.logb a (a ^ 2 * b) = 2 + Real.logb a b := by 
    have eq8 : Real.logb a (a ^ 2 * b) = Real.logb a (a ^ 2) + Real.logb a b := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    have eq9 : Real.logb a (a ^ 2) = 2 := by 
      calc 
        Real.logb a (a ^ 2) = Real.logb a ((a) ^ (2 : ℝ)) := by norm_num 
        _ = (2 : ℝ) * Real.logb a a := by 
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals 
            try linarith
        _ = (2 : ℝ) * (1 : ℝ) := by 
          rw [show Real.logb a a = 1 by
            rw [Real.logb_self_eq_one]
            all_goals 
              try linarith 
          ]
        _ = (2 : ℝ) := by 
          norm_num
    rw [eq9] at eq8
    linarith

  -- Derive an equation from h1, eq2, eq3, eq7
  -- Substitute to find that 2 * Real.logb a c = 1 + Real.logb a b
  have eq8 : 2 * Real.logb a c = 1 + Real.logb a b := by 
    rw [eq2, eq7] at h1 
    have eq10 : Real.logb a (a * c) = 1 + Real.logb a c := by 
      have h9a : Real.logb a (a * c) = Real.logb a a + Real.logb a c := by 
        rw [Real.logb_mul (by linarith) (by linarith)]
      have h9b : Real.logb a a = 1 := by 
        rw [Real.logb_self_eq_one]
        all_goals linarith
      rw [h9a, h9b]
    rw [eq3] at h1
    rw [eq10] at h1
    linarith

  -- Convert to equation without logb.
  -- Real.logb a c = Real.log c / Real.log a 
  -- Real.logb a b = Real.log b / Real.log a 
  have eq12 : Real.logb a c = Real.log c / Real.log a := by 
    field_simp [Real.logb]

  have eq13 : Real.logb a b = Real.log b / Real.log a := by 
    field_simp [Real.logb]

  have h14 : Real.log a > 0 := by 
    apply Real.log_pos
    linarith

  have h15 : Real.log b > 0 := by 
    apply Real.log_pos 
    linarith

  have h16 : Real.log c > 0 := by 
    apply Real.log_pos 
    linarith

  -- Convert eq8 into equation without logb
  have eq17 : 2 * (Real.log c / Real.log a) = 1 + (Real.log b / Real.log a) := by 
    rw [eq12, eq13] at eq8 
    linarith

  -- Simplify to get 2 * Real.log c = Real.log a + Real.log b
  have eq18 : 2 * Real.log c = Real.log a + Real.log b := by 
    have h14' : Real.log a ≠ 0 := by 
      linarith 
    have eq19 : 2 * (Real.log c / Real.log a) = 1 + (Real.log b / Real.log a) := eq17 
    have eq20 : 2 * Real.log c = Real.log a + Real.log b := by
      have eq21 : 2 * (Real.log c / Real.log a) * Real.log a = (1 + (Real.log b / Real.log a)) * Real.log a := by 
        rw [eq19]
      have eq22 : 2 * (Real.log c / Real.log a) * Real.log a = 2 * Real.log c := by 
        field_simp [h14']
        <;> linarith 
      have eq23 : (1 + (Real.log b / Real.log a)) * Real.log a = Real.log a + Real.log b := by 
        field_simp [h14']
        <;> linarith 
      linarith [eq21, eq22, eq23]
    exact eq20

  -- Express $\log c(a \cdot b)$ using the properties of logarithms.
  have h2 : Real.logb c (a * b) = (Real.log (a * b)) / (Real.log c) := by 
    field_simp [Real.logb]

  have eq11 : Real.log (a * b) = Real.log a + Real.log b := by 
    rw [Real.log_mul (by linarith) (by linarith)]

  rw [h2]
  rw [eq11]
  field_simp [show Real.log c ≠ 0 by linarith]
  all_goals linarith [eq18]