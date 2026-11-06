import Mathlib

theorem algebra_196957 {f : ℝ → ℝ} (hf : ∀ x, f (x + 1 / x) = x ^ 3 + 1 / x ^ 3) (b : ℝ)
    (h : f 4 = b) : b = 52 := by

  have h1 := hf (2 + Real.sqrt 3)
  have h2 : (2 + Real.sqrt 3 : ℝ) + 1 / (2 + Real.sqrt 3) = (4 : ℝ) := by
    have h3 : (2 + Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have eq1 : (2 + Real.sqrt 3 : ℝ) + 1 / (2 + Real.sqrt 3) = 4 := by
      field_simp [h3]
      <;> 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact_mod_cast eq1
  
  have h4 : (1 / (2 + Real.sqrt 3) ) = (2 - Real.sqrt 3) := by
    have h5 : (2 + Real.sqrt 3 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have eq2 : (1 / (2 + Real.sqrt 3) ) = (2 - Real.sqrt 3) := by
      have eq3 : (2 - Real.sqrt 3) * (2 + Real.sqrt 3) = (1 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have eq4 : (1 / (2 + Real.sqrt 3) ) = (2 - Real.sqrt 3) := by
        field_simp [h5, show (2 - Real.sqrt 3) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        ]
        <;> 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), eq3]
      exact_mod_cast eq4
    exact_mod_cast eq2
  
  have h5 : (1 / ((2 + Real.sqrt 3) ^ 3) : ℝ) = ((2 - Real.sqrt 3) ^ 3 : ℝ) := by
    have h6 : (1 / ((2 + Real.sqrt 3) ^ 3) : ℝ) = ((1 / (2 + Real.sqrt 3) ) ^ 3 : ℝ) := by
      field_simp
    rw [h6, h4]
  -- The main computation
  have h6' : ((2 + Real.sqrt 3) ^ 3 + 1 / ((2 + Real.sqrt 3) ^ 3) : ℝ) = (52 : ℝ) := by
    rw [show (1 / ((2 + Real.sqrt 3) ^ 3) : ℝ) = ((2 - Real.sqrt 3) ^ 3 : ℝ) by exact_mod_cast h5]
    have h7 : ((2 + Real.sqrt 3) ^ 3 + (2 - Real.sqrt 3) ^ 3 : ℝ) = (52 : ℝ) := by
      have h8 : ((2 + Real.sqrt 3) + (2 - Real.sqrt 3) : ℝ) = (4 : ℝ) := by
        ring_nf
      have h9 : ((2 + Real.sqrt 3) * (2 - Real.sqrt 3) : ℝ) = (1 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith [sq_nonneg ((2 + Real.sqrt 3) ^ 2 - (2 - Real.sqrt 3) ^ 2), sq_nonneg ((2 + Real.sqrt 3) * (2 - Real.sqrt 3) - 1), sq_nonneg ((2 + Real.sqrt 3) + (2 - Real.sqrt 3) - 4), sq_nonneg ((2 + Real.sqrt 3) - (2 - Real.sqrt 3)), sq_nonneg ((2 + Real.sqrt 3) ^ 2 + (2 - Real.sqrt 3) ^ 2 - 10), sq_nonneg ((2 + Real.sqrt 3) * (2 - Real.sqrt 3) * (2 + Real.sqrt 3) * (2 - Real.sqrt 3) - 1)]
    nlinarith
  
  rw [h2] at h1
  have eq4 : b = 52 := by
    linarith [h1, h6', h]

  exact_mod_cast eq4