import Mathlib

theorem inequalities_50225 (a b : ℤ) (c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : (a + 1) / (b + c) = b / a) : 1 ≤ c := by 
  have h1 : (a : ℝ) > 0 := by exact_mod_cast (show (0 : ℤ) < a by linarith)
  have h2 : (b : ℝ) > 0 := by exact_mod_cast (show (0 : ℤ) < b by linarith)
  have h3 : (b + c : ℝ) > 0 := by
    have h4 : (b : ℝ) > 0 := by exact_mod_cast (show (0 : ℤ) < b by linarith)
    linarith 
  have h5 : (a + 1 : ℝ) / (b + c) = (b : ℝ) / (a : ℝ) := by
    simpa using h
  -- Cross multiply (a + 1) * a = b * (b + c)
  have h6 : (a : ℝ) * (a + 1 : ℝ) = (b : ℝ) * (b + c : ℝ) := by
    have h7 : (a : ℝ) ≠ 0 := by linarith 
    have h8 : (b + c : ℝ) > 0 := by linarith
    field_simp [h7] at h5 ⊢
    nlinarith
  have eq1 : (a : ℝ) ^ 2 + (a : ℝ) = (b : ℝ) ^ 2 + (b : ℝ) * c := by
    nlinarith 
  by_contra h7 
  push_neg at h7 
  -- We need to derive a contradiction from c < 1.
  have h8 : (a : ℝ) ^ 2 + (a : ℝ) = (b : ℝ) ^ 2 + (b : ℝ) * c := eq1 
  have h11 : (a : ℝ) < (b : ℝ) := by 
    by_contra h_ange 
    push_neg at h_ange 
    have h12 : (a : ℝ) ≥ (b : ℝ) := h_ange 
    have h13 : (a : ℝ) ^ 2 + (a : ℝ) ≥ (b : ℝ) ^ 2 + (b : ℝ) := by 
      nlinarith [ sq_nonneg ((a : ℝ) - (b : ℝ) : ℝ), h12, 
        mul_pos h1 h2 
      ]
    have h14 : (b : ℝ) * c ≥ (b : ℝ) := by
      nlinarith [ eq1, h13 
      ]
    have h15 : (c : ℝ) ≥ 1 := by 
      have hb' : (b : ℝ) > 0 := h2 
      nlinarith 
    linarith 
  have h16 : (a : ℝ) ≤ (b - 1 : ℝ) := by 
    have h15 : a ≤ b - 1 := by 
      by_contra h17 
      push_neg at h17 
      have h18 : a ≥ b := by omega 
      have h19 : (a : ℝ) ≥ (b : ℝ) := by exact_mod_cast h18 
      linarith [h11, h19] 
    have h16 : (a : ℝ) ≤ (b - 1 : ℝ) := by 
      exact_mod_cast h15 
    linarith 
  -- If (a : ℝ) ≤ (b - 1 : ℝ), then (a : ℝ)^2 + (a : ℝ) ≤ (b - 1 : ℝ)^2 + (b - 1 : ℝ) = (b^2 - b)
  have h17 : (a : ℝ) ^ 2 + (a : ℝ) ≤ (b - 1 : ℝ) ^ 2 + (b - 1 : ℝ) := by 
    nlinarith [ sq_nonneg (( (a : ℝ) - (b - 1 : ℝ) ) : ℝ), 
      h16, 
      mul_pos h1 h2 
    ]
  -- Substituting (a : ℝ)^2 + (a : ℝ) in eq1 using h17: (b : ℝ)^2 + (b : ℝ)*c ≤ (b^2 - b) : b * c ≤ -b
  have h18 : (b : ℝ) * c ≤ - (b : ℝ) := by 
    nlinarith [ eq1, h17 
    ]
  -- Since (b : ℝ) > 0, dividing by b: (c : ℝ) ≤ -1
  have h19 : (c : ℝ) ≤ -1 := by 
    have hb' : (b : ℝ) > 0 := h2 
    nlinarith 
  linarith