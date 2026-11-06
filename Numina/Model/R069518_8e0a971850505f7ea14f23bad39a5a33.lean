import Mathlib
open Mathlib

theorem algebra_93528 (x : ℝ) (h : ∃ a d : ℝ, (10 + 2 + 5 + 2 + 4 + 2 + x) / 7 = a + d ∧
(10 + 2 + 5 + 2 + 4 + 2 + x) / 7 + d = 10 ∧ (10 + 2 + 5 + 2 + 4 + 2 + x) / 7 + 2 * d = 2 ∧
(10 + 2 + 5 + 2 + 4 + 2 + x) / 7 + 3 * d = 5 ∧ (10 + 2 + 5 + 2 + 4 + 2 + x) / 7 + 4 * d = 4 ∧
(10 + 2 + 5 + 2 + 4 + 2 + x) / 7 + 5 * d = 2) : x = 20 := by 
  rcases h with ⟨a, d, h₁, h₂, h₃, h₄, h₅, h₆⟩
  linarith