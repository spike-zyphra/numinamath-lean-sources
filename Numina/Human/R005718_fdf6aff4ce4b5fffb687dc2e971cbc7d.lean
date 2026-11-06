import Mathlib

open Nat

/-
Problem: If five fair coins are flipped simultaneously, what is the probability that at least three of them show heads?
-/
theorem Combinatorics_609584
    (N : n = 5)
    (PH : ph = 1 / 2)
    (PT : pt = 1 - ph)
    (A₁ : a₁ = a₂ + a₃ + a₄)
    (UP₁ : up₁ = 3)
    (UP₂ : up₂ = 4)
    (UP₃ : up₃ = 5)
    (A₂ : (a₂ : ℝ) = choose n up₁ * ph ^ up₁ * pt ^ (n - up₁)) 
    (A₃ : (a₃ : ℝ) = choose n up₂ * ph ^ up₂ * pt ^ (n - up₂)) 
    (A₄ : (a₄ : ℝ) = choose n up₃ * ph ^ up₃ * pt ^ (n - up₃)) :
    a₁= (1 / 2 : ℝ) := by 

  --Conclusion: The total probability a₁ equals 1/2.
  norm_num [Nat.choose, N, PH, PT, A₁, UP₁, UP₂, UP₃, A₂, A₃, A₄] at *   