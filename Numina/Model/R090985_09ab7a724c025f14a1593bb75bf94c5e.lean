import Mathlib

theorem number_theory_146302 :
    IsLeast {k | ∃ n m, n > m ∧ m ≥ 1 ∧ (42 ^ n) % 100 = (42 ^ m) % 100 ∧ k = m + n} 24 := by
  constructor
  · -- Let's verify the answer: n = 22, m = 2
    use 22, 2
    all_goals norm_num
    <;> omega
  · -- Now the hard part: proving that 24 is the minimum
    rintro k ⟨n, m, hn, hm, heq, rfl⟩
    by_contra h
    push_neg at h
    -- We now need to assume $m + n < 24$ and derive a contradiction
    have h4 : m < 12 := by
      nlinarith
    have h5 : n ≤ 23 := by
      nlinarith [show m < 12 by nlinarith]
    interval_cases m <;> interval_cases n <;> norm_num at heq ⊢ <;> omega