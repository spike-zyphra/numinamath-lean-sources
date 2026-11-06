import Mathlib

open Nat

/-
Kate has four red socks and four blue socks. If she randomly divides these eight socks into four pairs, what is the probability that none of the pairs will be mismatched? That is, what is the probability that each pair will consist either of two red socks or of two blue socks?
-/

theorem combinatorics_611259 
    (Red : k₁ = 4)
    (Blue : k₂ = 4)
    (All : k₃ = k₁ + k₂) : 
    (k₁.factorial / ((k₁ / 2).factorial * 2 ^ (k₁ / 2))) *
    (k₂.factorial / ((k₂ / 2).factorial * 2 ^ (k₂ / 2))) / 
    (k₃.factorial / ((k₃ / 2).factorial * 2 ^ (k₃ / 2))) = (3 : ℝ) / 35 := by 
    
  norm_num [Nat.factorial, Red, Blue, All]