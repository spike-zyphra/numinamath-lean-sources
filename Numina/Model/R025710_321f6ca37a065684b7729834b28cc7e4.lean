import Mathlib

theorem number_theory_13659 :
    IsLeast {x : ℕ | ∃ n : ℕ, x > 0 ∧ n > 0 ∧ x^2 + 2020 = n^2} 96 := by
  constructor
  · -- Proving 96 is in the set
    use 106
    all_goals norm_num
  · -- Proving no number less than 96 is in the set
    intro x hx
    rcases hx with ⟨n, hx_pos, hn_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : n < 107 := by 
      nlinarith [h_eq, show x < 96 from by linarith, show x > 0 from by linarith, show n > 0 from by linarith]
    have h2 : n ≤ 106 := by 
      omega
    have h3 : x ≤ 95 := by 
      omega
    interval_cases n <;> interval_cases x <;> omega