import Mathlib

theorem number_theory_167755 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      x = a^2 + b^2 + c^2 ∧ a^2 + b^2 > c^2 ∧ b^2 + c^2 > a^2 ∧ c^2 + a^2 > b^2} 77 := by
  constructor
  · -- Let's prove that 77 is achievable with sides 4, 5, 6.
    use 4, 5, 6
    all_goals norm_num 
  · -- Now, we prove that there is no element in the set less than 77
    intro x h
    rcases h with ⟨a, b, c, ha, hb, hc, hneab, hneac, hnebc, hx, h1, h2, h3⟩
    by_contra h'
    push_neg at h'
    rw [hx] at h'
    have h4 : a^2 + b^2 + c^2 < 77 := by linarith
    have h5 : a ≤ 8 := by
      nlinarith [sq_nonneg (b : ℕ), sq_nonneg (c : ℕ)]
    have h6 : b ≤ 8 := by
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (c : ℕ)]
    have h7 : c ≤ 8 := by
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ)]
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega