import Mathlib

/-
Problem Analysis: 
Probability of Two Students Being Assigned to the Same Class
-/
theorem combinatorics_609221 
  (n m s k : ℕ)
  (hn : n = 100)
  (hm : m = 60)
  (hs : s = 3)
  (hk : k = m / s) : 
  (m * (m - 1) / (n * (n - 1))) * ((k - 1) / (m - 1)) = (19 / 165 : ℝ) := by 
  
  norm_num [hk, hs, hm, hn]
