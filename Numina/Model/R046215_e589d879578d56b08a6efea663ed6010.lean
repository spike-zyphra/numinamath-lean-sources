import Mathlib

theorem number_theory_18599 :
    IsLeast {k | ∃ m n, m > 0 ∧ n > 0 ∧ Nat.gcd m n = 6 ∧ Nat.lcm m n = 126 ∧ k = m + n} 60 := by
  constructor
  · -- Show that 60 is in the set
    use 18, 42
    all_goals norm_num [Nat.gcd, Nat.lcm]
 
  · -- Show that 60 is minim
    intro k hk
    rcases hk with ⟨m, n, hm, hn, hg, hl, hk⟩
    by_contra h
    push_neg at h
    have h1 : m ≤ 58 := by
      omega
    have h2 : n ≤ 58 := by
      omega
    interval_cases m <;> interval_cases n
    <;> norm_num [Nat.gcd, Nat.lcm] at hg hl
    <;> omega