import Mathlib

/-!
In RNG baseball, a team of infinitely many players takes turns at bat. 
Each player on their turn chooses a number `n ∈ {0,1,2,3,4}` uniformly at random. 
- If `n = 0`, the game ends immediately.
- If `n > 0`, the player and all others currently on bases move forward `n` positions (mod 4). 
  If any player returns to or passes home base (position 0), they score a point and leave the field.

We define `expectedScore` to be the expected total number of points scored in such a game.

The final result shows that `expectedScore = 409 / 125`.
-/

noncomputable def expectedScore : ℚ :=
  let P₃ := 4 / 5
  let P₂ := (1 : ℚ) / 5 * (P₃ + 3)         -- P₂ = (1/5)(P₃ + 3)
  let P₁ := (1 : ℚ) / 5 * (P₂ + P₃ + 2)    -- P₁ = (1/5)(P₂ + P₃ + 2)
  let P₀ := (1 : ℚ) / 5 * (P₁ + P₂ + P₃ + 1) -- P₀ = (1/5)(P₁ + P₂ + P₃ + 1)
  let sum := 1 / (1 - 4 / 5 : ℚ)           -- geometric sum = 1 / (1 - 4/5) = 5
  P₀ * sum

-- Final theorem statement
theorem Combinatorics_609780 : expectedScore = 409 / 125 := by
  -- directly unfold and compute the expression
  unfold expectedScore
  -- evaluate everything numerically
  norm_num
