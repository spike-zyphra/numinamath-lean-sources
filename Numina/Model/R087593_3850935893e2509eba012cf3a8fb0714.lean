import Mathlib

theorem number_theory_101287 :
    IsLeast {k | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m > n ∧ (2012 ^ m) % 1000 = (2012 ^ n) % 1000 ∧ k = m + n} 104 := by
  constructor
  · -- First, prove 104 can be achieved
    use 102, 2
    all_goals norm_num
  · -- Now prove that 104 is the smallest
    intro k hk
    rcases hk with ⟨m, n, hm, hn, hmn, heq, hk⟩
    by_contra h
    push_neg at h
    have h1 : m + n < 104 := by omega
    have h2 : m < 104 := by omega
    have h3 : n < 104 := by omega
    interval_cases m <;> interval_cases n
    <;> norm_num [Nat.pow_mod] at heq
    all_goals omega