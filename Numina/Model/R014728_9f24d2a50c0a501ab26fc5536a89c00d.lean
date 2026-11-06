import Mathlib

theorem number_theory_95100 :
    IsLeast {x | ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      Even a ∧ Even b ∧ Even c ∧ Even d ∧ x = (a + b + c + d) / 4 ∧ x ≥ 5} 5 := by
  constructor
  · -- Show 5 is in the set
    use 2, 4, 6, 8
    all_goals norm_num [Nat.even_iff]
  · -- Show no number less than 5 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hne1, hne2, hne3, hne4, hne5, hne6, he1, he2, he3, he4, hx, hx5⟩
    linarith