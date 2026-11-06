import Mathlib

theorem number_theory_37023 :
    IsLeast {x | ∃ n m : ℕ, n ≤ 2007 ∧ 2007 ≤ m ∧ n ^ n ≡ -1 [ZMOD 5] ∧ m ^ m ≡ -1 [ZMOD 5] ∧ x = m - n} 7 := by
  constructor
  · -- Show that 7 is indeed in the set.
    use 2002, 2009
    all_goals native_decide
  · -- Show that 7 is the smallest such value.
    intro x hx
    rcases hx with ⟨n, m, hn1, hm1, h1, h2, heq⟩
    by_contra h
    push_neg at h
    have h3 : x < 7 := by linarith
    rw [heq] at h3
    have h4 : m < n + 7 := by omega
    have hn2 : n ≥ 1999 := by
      omega
    have h5 : m ≤ n + 6 := by omega
    interval_cases n <;> interval_cases m <;> norm_num [Int.ModEq] at h1 h2 <;> omega