import Mathlib

theorem number_theory_243835 (n : ℕ) :
    IsLeast {n | ∃ k, (2^8 + 2^11 + 2^n) = k^2} 12 := by 
  constructor
  · -- Show that 12 is in the set
    use 80
    all_goals norm_num
  · -- Show that no smaller element is in the set
    intro n hn
    rcases hn with ⟨k, hk⟩
    by_contra h
    push_neg at h
    have h1 : n < 12 := by linarith
    interval_cases n <;> try { 
      by_cases h' : k ≤ 128
      · interval_cases k <;> omega
      · 
        push_neg at h'
        have h7 : k > 128 := by linarith
        have h8 : k ≤ 256 := by
          nlinarith
        interval_cases k <;> omega
    }
    <;> try { nlinarith }