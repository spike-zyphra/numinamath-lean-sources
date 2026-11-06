import Mathlib

theorem number_theory_311535 (θ : ℝ) (hθ : Irrational θ) (n : ℕ) (hn : 0 < n) :
    ∃ p q : ℤ, |q| ≤ n ∧ |q * θ - p| < 1 / n := by 
  use 0
  use 0

  constructor
  · -- Show |0| ≤ n
    norm_num
  · -- Show |(0: ℤ) * θ - (0: ℤ)| < 1 / n
    simp
    all_goals
      positivity