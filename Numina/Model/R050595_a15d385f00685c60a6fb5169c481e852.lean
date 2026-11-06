import Mathlib

def isSnail (n : ℕ) := ∃ a b c, n = 1000 * a + 100 * b + 10 * c + a + b + c

theorem number_theory_204878 : ∃ m, isSnail m ∧ ∃ k, m = k ^ 2 := by 
  use 1089
  constructor
  · -- Show 1089 is a snail number
    refine' ⟨0, 0, 99, by norm_num⟩
  · -- Show there exists k such that 1089 = k^2
    use 33
    norm_num