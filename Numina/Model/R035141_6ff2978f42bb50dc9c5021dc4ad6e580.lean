import Mathlib

theorem number_theory_225444 (m n : ℕ) : m^5 + n^2 = 1700 ↔ (m=4 ∧ n=26) := by
  constructor
  · -- First part: if m^5 + n^2 = 1700, then (m=4 and n=26)
    intro h
    have h1 : m ≤ 4 := by
      by_contra h2
      push_neg at h2
      have h2' : m ≥ 5 := by omega
      have h3 : m^5 ≥ 3125 := by
        have : m ≥ 5 := by linarith
        have h4 : m^5 ≥ 5^5 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h4 ⊢
        linarith
      have h4 : m^5 + n^2 ≥ 3125 := by linarith [show m^5 ≥ 3125 from by linarith, show n^2 ≥ 0 from by positivity]
      nlinarith
    have h2 : m ≤ 4 := h1
    have h3 : n ≤ 41 := by
      nlinarith [show m^5 ≥ 0 by positivity, h]
    interval_cases m <;> try { 
      interval_cases n <;> norm_num at h ⊢
      all_goals
        try { 
          omega 
        } <;> try { 
          tauto 
        }
    }
  · -- Second part: if (m=4 and n=26), then m^5 +n^2=1700
    rintro ⟨rfl, rfl⟩
    all_goals
    norm_num