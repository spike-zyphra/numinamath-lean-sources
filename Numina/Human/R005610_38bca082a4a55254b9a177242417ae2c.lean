import Mathlib

/-
Tim and Allen are playing a match of tenus. In a match of tenus, the two players play a series of games, each of which is won by one of the two players. The match ends when one player has won exactly two more games than the other player, at which point the player who has won more games wins the match. In odd-numbered games, Tim wins with probability $3 / 4$, and in the even-numbered games, Allen wins with probability $3 / 4$. What is the expected number of games in a match?
-/
theorem combinatorics_609112 
    (E : ℤ → ℝ) 
    (E₁ : E 1 = 1 + 3 / 4 * E 0 + 1 / 4 * E 2) 
    (hE₁ : E (- 1) = 1 + 3 / 4 * E (- 2) + 1 / 4 * E 0) 
    (E₀ : E 0 = 1 + 3 / 4 * E 1 + 1 / 4 * E (-1)) 
    (E₂ : E 2 = 0)
    (hE₂ : E (- 2) = 0) :
    E 0 = (16 / 3 : ℝ) := by

  -- Rename hypotheses for clarity
  have h₁ : E 1 = 1 + 3 / 4 * E 0 + 1 / 4 * E 2 := E₁

  have h₂ : E (-1) = 1 + 3 / 4 * E (-2) + 1 / 4 * E 0 := hE₁

  have h₃ : E 0 = 1 + 3 / 4 * E 1 + 1 / 4 * E (-1) := E₀
  
  have h₄ : E 2 = 0 := E₂

  have h₅ : E (-2) = 0 := hE₂
  
  -- Simplify E(1) using E(2) = 0
  have h₆ : E 1 = 1 + 3 / 4 * E 0 := by

    rw [h₁, h₄]

    ring_nf
    
  -- Simplify E(-1) using E(-2) = 0
  have h₇ : E (-1) = 1 + 1 / 4 * E 0 := by

    rw [h₂, h₅]

    ring_nf
  
  -- Substitute simplified E(1) and E(-1) into E(0) equation
  have h₈ : E 0 = 1 + 3 / 4 * E 1 + 1 / 4 * E (-1) := h₃

  have h₉ : E 0 = (16 / 3 : ℝ) := by

    rw [h₈, h₆, h₇]

    -- Expand and simplify the right-hand side
    ring_nf at *

    -- Solve the linear equation using field arithmetic
    linarith
    
  exact h₉
