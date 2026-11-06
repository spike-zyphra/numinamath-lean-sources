import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189796 {y : ℝ → ℝ} (hy : y = λ x => sqrt (logb 0.3 ((x - 1) / (x + 5))))
  (x : ℝ) (hx : x > 1) :
  y x ∈ Ioi 0 := by
  rw [hy]
  have h1 : sqrt (logb (0.3 : ℝ) ((x - 1) / (x + 5))) > 0 := by
    have h2 : logb (0.3 : ℝ) ((x - 1) / (x + 5)) > 0 := by
      have h3 : (x - 1 : ℝ) / (x + 5) < (1 : ℝ) := by 
        have h4 : x + 5 > 0 := by linarith 
        apply (div_lt_iff₀ h4).mpr 
        linarith 
      have h4 : logb (0.3 : ℝ) ((x - 1) / (x + 5)) > logb (0.3 : ℝ) (1 : ℝ) := by
        apply Real.logb_lt_logb_of_base_lt_one 
        all_goals 
          norm_num at *
          all_goals
            have h5 : (x - 1 : ℝ) / (x + 5) > 0 := by
              apply div_pos 
              all_goals 
                linarith 
            nlinarith 
      have h5 : logb (0.3 : ℝ) (1 : ℝ) = 0 := by 
        norm_num [logb_one] 
      linarith 
    have h6 : sqrt (logb (0.3 : ℝ) ((x - 1) / (x + 5))) > 0 := by
      apply Real.sqrt_pos.2 
      all_goals
        linarith [h2] 
    exact h6 
  exact h1