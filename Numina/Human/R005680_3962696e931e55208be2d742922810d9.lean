import Mathlib

/-
Problem:
Calvin has a bag containing 50 red balls, 50 blue balls, and 30 yellow balls. Given that after pulling out 65 balls at random (without replacement), he has pulled out 5 more red balls than blue balls, what is the probability that the next ball he pulls out is red?
-/
theorem combinatorics_609372 
    (r b y : ℕ) 
    (h₀ : r = 50) 
    (h₁ : b = 50) 
    (h₂ : y = 30) 
    (h₃ : r - b = 5) :
    (r : ℝ) / (r + b + y - 65) = 9 / 26 := by 

  rw [h₀ , h₁ , h₂]

  omega