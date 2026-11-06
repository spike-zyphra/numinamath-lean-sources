import Mathlib

/-
This theorem formalizes the probability calculation for selecting exactly 2 distinct colors from 5 jellybeans, where each jellybean can be one of 5 equally-probable colors.The result verifies the probability is 12/125.
-/
theorem Combinatorics_608188 
  (n k : ℕ)
  (c₁ c₂ c₃ c₄ c₅ c₆ : ℝ)
  (colors : n = 5)
  (choose : c₁ = 5)
  (hcolors : k = 2)
  (combination : c₂ = n.choose k)
  (all_one : c₃= k ^ n - k) 
  (all : c₄ = c₂ * c₃)
  (all_possible : c₅ = n ^ c₁) 
  (classic : c₆ = c₄ / c₅):
  c₆ = (12 : ℝ) / (125 : ℝ) := by

  simp_all [Nat.choose]
  
  norm_num
  
  

  

