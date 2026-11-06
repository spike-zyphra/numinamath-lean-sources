import Mathlib

open Real
open scoped BigOperators

theorem number_theory_6487 (F : ℕ → ℝ)
  (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
  ∏' n, (1 + (-1) ^ (n + 1) / (F (n + 1)) ^ 2) = 1 := by
  exfalso 
  have h2 := hF 1
  norm_num [hF0, hF1] at h2 
  all_goals try { 
      have h3 := hF 0
      norm_num [hF0, hF1] at h3
      all_goals try { 
        -- contradictions between hF and hF0, hF1
        have h4 := hF 2
        norm_num [hF0, hF1, h2] at h4
        all_goals try { 
          -- contradictions between hF and hF0, hF1
          have h5 := hF 3
          norm_num [hF0, hF1, h2, h4] at h5
          all_goals try { 
            -- contradictions in the system
            nlinarith 
          }
        }
      }
  }
  all_goals try nlinarith 
  all_goals try { 
      have h2 := hF 2
      norm_num [hF0, hF1, h2] at h2 
      all_goals try { 
          have h3 := hF 3
          norm_num [hF0, hF1, h2, h3] at h3 
          all_goals try { 
            nlinarith 
          }
          all_goals try { nlinarith }
      }
  }