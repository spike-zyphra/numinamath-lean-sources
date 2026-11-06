import Mathlib

open Finset

open Nat

/-
Calculate the number of ways to choose k non-adjacent elements from n positions. If k is greater than (n + 1) / 2, it's impossible to choose k non-adjacent elements, so the result is 0. Otherwise, the result is the binomial coefficient C(n - k + 1, k).
-/
def non_adjacent_comb (n k : ℕ) : ℕ :=
  if k > (n + 1) / 2 then 0 else choose (n - k + 1) k

/-
Prove that when arranging 4 red marbles and 8 blue marbles in a circle,
the probability that no two red marbles are adjacent is 7/33.
-/
theorem combinatorics_608157 
    (red blue : ℕ) 
    (hred : red = 4) 
    (hblue : blue = 8) :
    (non_adjacent_comb (red + blue - 1) red : ℝ) / (choose (red + blue - 1) red : ℝ) = (7 / 33 : ℝ) := by

  rw [hred, hblue]

  simp [non_adjacent_comb]

  have h₁ : choose 8 4 = 70 := by decide

  have h₂ : choose 11 4 = 330 := by decide

  rw[h₁,h₂]

  ring


  