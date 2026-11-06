import Mathlib

theorem algebra_264785 (p q r : ℤ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h : p + 1 / (q + 1 / r : ℚ) = 25 / 19) : q = 3 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : (p : ℚ) + 1 / (q + 1 / r : ℚ) = (25 / 19 : ℚ) := by
    simpa using h

  have hp1 : p = 1 := by
    by_contra h'
    push_neg at h'
    have hp2 : p ≥ 2 := by omega
    have h4 : (p : ℚ) ≥ (2 : ℚ) := by exact_mod_cast hp2
    have h6 : (p : ℚ) + 1 / (q + 1 / r : ℚ) ≥ (2 : ℚ) := by
      have hp2' : (p : ℚ) ≥ (2 : ℚ) := h4
      have h7 : (1 / (q + 1 / r : ℚ) : ℚ) ≥ (0 : ℚ) := by 
        apply div_nonneg
        norm_num
        have hq_pos : (q : ℚ) > (0 : ℚ) := by exact_mod_cast show q > (0 : ℤ) by omega
        have hr_pos : (r : ℚ) > (0 : ℚ) := by exact_mod_cast show r > (0 : ℤ) by omega
        have h10 : (1 / r : ℚ) > 0 := by
          apply div_pos
          norm_num
          exact_mod_cast show r > (0 : ℤ) by omega
        have h8 : (q + 1 / r : ℚ) > 0 := by
          have hq_pos : (q : ℚ) > 0 := by exact_mod_cast show q > (0 : ℤ) by omega
          have h10 : (1 / r : ℚ) > 0 := by 
            apply div_pos
            norm_num
            exact_mod_cast show r > (0 : ℤ) by omega
          nlinarith
        positivity
      linarith [hp2', h7]
    nlinarith [h1, h6, show (25 / 19 : ℚ) < (2 : ℚ) by norm_num]

  have h4 : (p : ℚ) = 1 := by
    exact_mod_cast hp1

  have h5 : (1 / (q + 1 / r : ℚ) : ℚ) = (6 / 19 : ℚ) := by
    nlinarith [h1, h4]

  have h6 : (q + 1 / r : ℚ) = (19 / 6 : ℚ) := by
    have h7 : (q + 1 / r : ℚ) > 0 := by
      have hq_pos : (q : ℚ) > (0 : ℚ) := by exact_mod_cast show q > (0 : ℤ) by omega
      have hr_pos : (r : ℚ) > (0 : ℚ) := by exact_mod_cast show r > (0 : ℤ) by omega
      have h10 : (1 / r : ℚ) > 0 := by 
        apply div_pos
        norm_num
        exact_mod_cast show r > (0 : ℤ) by omega
      have h8 : (q + 1 / r : ℚ) > 0 := by
        have hq_pos : (q : ℚ) > 0 := by exact_mod_cast show q > (0 : ℤ) by omega
        have h10 : (1 / r : ℚ) > 0 := by 
          apply div_pos
          norm_num
          exact_mod_cast show r > (0 : ℤ) by omega
        nlinarith
      linarith
    field_simp [(show (q + 1 / r : ℚ) ≠ 0 by linarith [h7])] at h5 ⊢
    all_goals nlinarith
    all_goals try { tauto }
  -- Convert the equation from rational to integer form
  have eq1 : (6 : ℚ) * (q * r : ℚ) + (6 : ℚ) = (19 : ℚ) * (r : ℚ) := by
    have h7 : (q + 1 / r : ℚ) = (19 / 6 : ℚ) := h6
    field_simp [(show (r : ℚ) ≠ 0 by exact_mod_cast show r ≠ 0 by omega)] at h7 ⊢
    nlinarith [h7, show (r : ℚ) ≠ 0 by exact_mod_cast show r ≠ 0 by omega]

  -- Convert rational equation to integer equation
  have eq2 : 6 * (q * r : ℤ) + 6 = 19 * r := by
    have eq3 : (6 * (q * r : ℚ) + 6 : ℚ) = (19 * r : ℚ) := by
      nlinarith [eq1]
    have eq4 : (6 * (q * r : ℤ) + 6 : ℚ) = (19 * r : ℚ) := by
      exact_mod_cast eq3
    exact_mod_cast eq4
  -- Simplify the equation involving `q` and `r`
  have h_eq : r * (6 * q - 19) = -6 := by
    nlinarith [eq2]

  -- Since r > 0 and r divides -6, r must be a positive divisor of 6
  have h_eq4 : r ∣ 6 := by 
    use (19 - 6 * q)
    all_goals nlinarith [h_eq]

  have h_eq5 : r ≤ 6 := by
    apply Int.le_of_dvd (by omega) h_eq4
  -- From r > 0 and r ≤ 6, we can do exhaustive checking of r ∈ {1, 2, 3, 4, 5, 6} cases
  have h_eq6 : r ≥ 1 := by 
    omega

  interval_cases r <;> try { 
    omega
  }
  all_goals try { 
    omega
  }
  all_goals try { 
    exfalso
    all_goals try { 
      tauto 
      all_goals omega 
    }
  }
  all_goals try { 
    omega 
    <;> try { 
      nlinarith 
    }
  }
  all_goals try { 
    try { 
      omega 
      all_goals try { tauto } 
    }
  }
  all_goals try { 
    try { 
      omega 
    }
    try { 
      exfalso
      <;> try { 
        omega 
        <;> try { 
          tauto 
          <;> try { 
            nlinarith 
          }
        }
      }
    }
  }
  all_goals try { 
    nlinarith 
  }