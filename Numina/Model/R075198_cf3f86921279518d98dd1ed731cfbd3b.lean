import Mathlib

theorem number_theory_2629 (r c : ℕ) (hr : r = 44) (hc : c = 13) :
    IsLeast {n | ∃ k, (r * c + n) = 20 * k} 8 := by
  rw [hr, hc]
  constructor
  · -- Show 8 is in the set
    use 29
    all_goals norm_num
  · -- Show no number less than 8 is in the set
    intro n hn
    rcases hn with ⟨k, hk⟩
    omega