import Mathlib

theorem number_theory_2166 :
    IsLeast {k : ℤ | k ^ 4 < 10 ^ 6} (-31) := by
        constructor 
        · -- Show that -31 is in the set
          norm_num 
        · -- Show that -31 is the smallest, so k >= -31 
          intro k 
          intro hk 
          have hk1 : k ^ 4 < 10 ^ 6 := hk 
          by_contra h 
          push_neg at h 
          have h2 : k <= -32 := by omega 
          have h3 : k ^ 4 ≥ (32 : ℤ) ^ 4 := by 
            nlinarith [sq_nonneg (k ^ 2 - 32 ^ 2), sq_nonneg (k ^ 2 + 32 ^ 2),
              sq_nonneg ((k ^ 2) ^ 2 - (32 ^ 2) ^ 2), sq_nonneg ((k ^ 2) ^ 2 + (32 ^ 2) ^ 2),
              sq_nonneg (k + 32), sq_nonneg (k - 32),
              sq_nonneg (k ^ 2), sq_nonneg (k ^ 4),
              show k ^ 4 >= 0 by positivity, show (32 : ℤ) ^ 4 > (10 ^ 6 : ℤ) by norm_num
            ] 
          norm_num at h3 
          linarith