import Mathlib

open Finset ProbabilityTheory BigOperators

/-
Problem : 
In the game of rock-scissors (a variant of rock-paper-scissors where paper is forbidden), the computer plays rock with 50% probability and scissors with 50% probability. The optimal strategy for the player is to always play rock, resulting in a 50% win rate per game (when the computer plays scissors). We need to find the probability that the player wins at least 4 out of 8 games.
-/
inductive GameResult
  | win   
  | draw  
  | lose

theorem Combinatorics_609066
    (computer_scissors_prob : ℝ) 
    (h_scissors : computer_scissors_prob = 1 / 2)
    (p : ℕ → ℝ)
    (hp : ∀ n, p n = (Nat.choose 8 n : ℝ) / (2 ^ 8)) :
    ∑ n in Icc 4 8, p n = 163 / 256 := by

  -- Confirm the computer's strategy
  have h₁ : computer_scissors_prob = 1 / 2 := by linarith
  
  -- Expand the probability mass function for n=4 to 8
  have h₂ : p 4 = (Nat.choose 8 4 : ℝ) / (2 ^ 8) := by exact hp 4

  have h₃ : p 5 = (Nat.choose 8 5 : ℝ) / (2 ^ 8) := by exact hp 5

  have h₄ : p 6 = (Nat.choose 8 6 : ℝ) / (2 ^ 8) := by exact hp 6

  have h₅ : p 7 = (Nat.choose 8 7 : ℝ) / (2 ^ 8) := by exact hp 7

  have h₆ : p 8 = (Nat.choose 8 8 : ℝ) / (2 ^ 8) := by exact hp 8
  
  -- Expand the summation into individual terms
  have h₇ : ∑ n in Icc 4 8, p n = p 4 + p 5 + p 6 + p 7 + p 8 := by

    norm_num [Finset.sum_Icc_succ_top, Finset.Icc_self, hp, Finset.sum_range_succ, Nat.choose_succ_succ]
  
  -- Substitute the combinatorial values and compute the sum
  rw [h₇]

  simp [h₂, h₃, h₄, h₅, h₆]

  norm_num [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_self]