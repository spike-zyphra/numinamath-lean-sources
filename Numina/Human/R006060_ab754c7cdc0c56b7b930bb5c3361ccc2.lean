import Mathlib

open Finset

/-
Every second, Andrea writes down a random digit uniformly chosen from the set $\{1,2,3,4\}$. She stops when the last two numbers she has written sum to a prime number. What is the probability that the last number she writes down is 1 ?
-/

theorem combinatorics_611330 
    {p : ℕ → ℝ} 
    (hp2 : p 2 = 1 / 2) 
    (hp4 : p 4 = 1 / 2)
    (hp1 : p 1 = (1 + p 3) / 4) 
    (hp3 : p 3 = (p 1 + p 3) / 4) :
    (1 / 4) * (p 1 + p 2 + p 3 + p 4) = 15 / 44 := by

  -- Prove that p₁ = 3 * p₃ using linear arithmetic with given equations
  have eq1 : p 1 = 3 * p 3 := by
    linarith
  
  -- Solve for p₃ using the relationship p₁ = 3 * p₃ and given equations
  have eq2 : p 3 = 1 / 11 := by
    rw [eq1] at hp1
    linarith

  -- Calculate p₁ using the derived value of p₃
  have eq3 : p 1 = 3 / 11 := by
    rw [eq2] at eq1
    linarith
  
  linarith