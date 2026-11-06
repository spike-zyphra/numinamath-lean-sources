import Mathlib

theorem number_theory_94579 (n : ℕ) (h : n = 2023) :
    IsLeast {k | ∃ r l : ℕ, r * 5 - l * 3 = n ∧ k = r + l} 411 := by 
  rw [h]
  constructor
  · -- Show 411 is in the set
    use 407, 4
    all_goals omega
  · -- Show there is no smaller number in the set
    intro k hk
    rcases hk with ⟨r, l, h_eq, hk⟩
    omega