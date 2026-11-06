import Mathlib

open Real Nat

/-
What is the probability that Victor stops with 2 socks of the same type? Assume Victor returns both socks to the drawer after each step.
-/
theorem combinatorics_609365 
    (c s t : ℕ) 
    (C : c = 2)   -- c = number of complex socks = 2
    (S : s = 2)   -- s = number of synthetic socks = 2
    (T : t = 2) : -- t = number of trigonometric socks = 2
    (choose c c + choose s s + choose t t) / (choose c c + choose s s + choose t t + choose s 1 * choose c 1) = (3 / 7 : ℝ) := by

  -- Substitute c=2, s=2, t=2 and simplify using numerical normalization
  norm_num [C, S, T]