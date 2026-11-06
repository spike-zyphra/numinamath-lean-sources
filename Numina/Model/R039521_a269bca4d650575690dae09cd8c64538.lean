import Mathlib

theorem number_theory_143259 :
    IsLeast {x | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m < n ∧ (1978 ^ m) % 1000 = (1978 ^ n) % 1000 ∧ x = m + n} (3 + 103) := by
  constructor
  · -- Show 3 + 103 is in the set.
    use 3, 103
    all_goals norm_num
  · -- Show that 3 + 103 is the least element in the set
    intro x hx
    rcases hx with ⟨m, n, hm, hn, hmn, heq, hx⟩
    by_contra h
    push_neg at h
    have h1 : m + n < 106 := by linarith [hx, h]
    have h2 : n ≤ 105 := by
      omega
    have h3 : m < 105 := by
      omega
    interval_cases m <;> try { 
      omega 
    } <;> try { 
      interval_cases n <;> omega 
    }