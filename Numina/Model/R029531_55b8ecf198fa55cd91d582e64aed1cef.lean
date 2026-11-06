import Mathlib

theorem number_theory_19279 :
    IsLeast {x | ∃ m n, x = m + n ∧ m > 0 ∧ n > 0 ∧
    Nat.gcd m n = 8 ∧ Nat.lcm m n = 112} 72 := by
  constructor
  · -- Show that 72 is in the set
    use 56, 16
    all_goals norm_num
  · -- Show that 72 is the least in the set
    intro x hx 
    rcases hx with ⟨m, n, h1, hm1, hn1, h2, h3⟩ 
    by_contra h
    push_neg at h 
    have h4 : m + n < 72 := by 
      omega 
    have h5 : m ≤ 70 := by 
      omega 
    have h6 : n ≤ 70 := by 
      omega 
    interval_cases m <;> interval_cases n 
    <;> norm_num [Nat.gcd, Nat.lcm] at h2 h3 h1 ⊢ 
    <;> omega