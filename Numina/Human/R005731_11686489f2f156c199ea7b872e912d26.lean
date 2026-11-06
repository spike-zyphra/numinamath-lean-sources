import Mathlib

open Real

/-
Problem Analysis:
Steph Curry wins a game by reaching exactly 5 points. Each turn:
1. Flip a fair coin: heads → attempt a 3-point shot (success rate 1/2), tails → take a free throw (always successful).
2. The game ends when points reach exactly 5 (win) or exceed 5 (lose).
-/
theorem combinatorics_609633
  {p : ℕ → ℝ}  
  (hp5 : p 5 = 1)
  (hpn₁ : ∀ n ≥ 6 , p n = 0)
  (hpn₂ : ∀ n ≤ 4 ,  
  p n = 1 / 4 * p (n + 3) + 1 / 2 * p (n + 1) + 1 / 4 * p n) :
  p 0 = 140 / 243 := by

  -- Step 1: Derive recurrence for n=4 (using hpn₂ since 4 ≤ 4)
  have t₁ : p 4 = 1 / 4 * p 7 + 1 / 2 * p 5 + 1 / 4 * p 4 := by 
    apply hpn₂
    norm_num 

  -- Step 2: Derive recurrence for n=3 (using hpn₂ since 3 ≤ 4)
  have t₂ : p 3 = 1 / 4 * p 6 + 1 / 2 * p 4 + 1 / 4 * p 3 := by 
    apply hpn₂  
    norm_num 

  -- Step 3: Derive recurrence for n=2 (using hpn₂ since 2 ≤ 4)
  have t₃ : p 2 = 1 / 4 * p 5 + 1 / 2 * p 3 + 1 / 4 * p 2 := by
     apply hpn₂
     norm_num  

  -- Step 4: Derive recurrence for n=1 (using hpn₂ since 1 ≤ 4)
  have t₄ : p 1 = 1 / 4 * p 4 + 1 / 2 * p 2 + 1 / 4 * p 1 := by
     apply hpn₂  
     norm_num 

  -- Step 5: Derive recurrence for n=0 (using hpn₂ since 0 ≤ 4)
  have t₅ : p 0 = 1 / 4 * p 3 + 1 / 2 * p 1 + 1 / 4 * p 0 := by
     apply hpn₂ 
     norm_num 

  -- Step 6: Use termination condition for n=7 (7 ≥ 6 ⇒ p(7)=0)
  have t₆ : p 7 = 0 := by
    apply hpn₁  
    norm_num  

  -- Step 7: Use termination condition for n=6 (6 ≥ 6 ⇒ p(6)=0)
  have t₇ : p 6 = 0 := by 
    apply hpn₁  
    norm_num  

  -- Step 8: Explicitly state the winning condition at n=5
  have t₈ : p 5 = 1 := by exact hp5  

  linarith