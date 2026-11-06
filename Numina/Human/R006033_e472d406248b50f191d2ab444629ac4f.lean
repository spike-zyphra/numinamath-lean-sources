import Mathlib
open Real

/-
Theorem: Probability that a best-of-9 series ends exactly at 7 games with Mathletes having a 2/3 chance of winning each game.
-/
theorem combinatorics_611215 
    (p : ℝ) 
    (hp : p = 2 / 3) :
    ((Nat.choose 6 2) * (p ^ 4) * (1 - p) ^ 2) * p + ((Nat.choose 6 2) * (1 - p) ^ 4 * p ^ 2) * (1 - p) = 20 / 81 := by

  -- Simplify the expression using numerical evaluation and the given equality hp
  norm_num [hp, Nat.choose]
