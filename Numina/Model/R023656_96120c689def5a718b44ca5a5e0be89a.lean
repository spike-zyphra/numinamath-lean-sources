import Mathlib

open Real

theorem algebra_4616 {f g : ℝ → ℝ} (hf : f = λ x => 1 + 2 * logb 2 x) (hg : g = λ x => logb x 2) :
    f (1 / 2) = g (1 / 2) ∧ f (Real.sqrt 2) = g (Real.sqrt 2) := by 
  constructor
  · -- Show f (1 / 2) = g (1 / 2)
    rw [hf, hg]
    have h1 : logb (2 : ℝ) (1 / 2 : ℝ) = -1 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
    have h2 : logb (1 / 2 : ℝ) (2 : ℝ) = -1 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
    have eq1 : (1 + 2 * logb (2 : ℝ) (1 / 2 : ℝ) : ℝ) = logb (1 / 2 : ℝ) (2 : ℝ) := by 
      have eq1 : logb (2 : ℝ) (1 / 2 : ℝ) = -1 := h1 
      have eq2 : logb (1 / 2 : ℝ) (2 : ℝ) = -1 := h2 
      rw [eq1, eq2]
      all_goals norm_num
    have h_eq : (1 + 2 * logb (2 : ℝ) (1 / 2 : ℝ) : ℝ) = (logb (1 / 2 : ℝ) (2 : ℝ) : ℝ) := by 
      linarith [eq1]
    simpa using h_eq 
  · -- Show f (Real.sqrt 2) = g (Real.sqrt 2)
    rw [hf, hg] 
    have h1 : logb (2 : ℝ) (Real.sqrt 2 : ℝ) = 1 / 2 := by 
      have h2 : Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h2]
      have h3 : logb (2 : ℝ) ((2 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by 
        rw [logb_rpow]
        all_goals norm_num
      rw [h3]
    have h41 : logb (Real.sqrt 2 : ℝ) (2 : ℝ) = 2 := by 
      have h401 : logb (Real.sqrt 2 : ℝ) (2 : ℝ) = (log (2 : ℝ) ) / (log (Real.sqrt 2 : ℝ) ) := by 
        field_simp [Real.logb]
      have h402 : log (Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) * log (2 : ℝ) := by 
        calc 
          log (Real.sqrt 2 : ℝ) = log ((2 : ℝ) ^ (1 / 2 : ℝ) ) := by 
            rw [Real.sqrt_eq_rpow]
          _ = (1 / 2 : ℝ) * log (2 : ℝ) := by 
            rw [log_rpow]
            all_goals norm_num 
      rw [h401, h402]
      have h43 : log (2 : ℝ) > 0 := by
        apply log_pos
        all_goals linarith 
      have h44 : log (2 : ℝ) ≠ 0 := by 
        linarith [h43] 
      field_simp [h43, h44]
      <;> linarith 
    have h5 : (1 + 2 * logb (2 : ℝ) (Real.sqrt 2 : ℝ) : ℝ) = (logb (Real.sqrt 2 : ℝ) (2 : ℝ) : ℝ) := by 
      rw [h1, h41]
      all_goals norm_num
    simpa using h5