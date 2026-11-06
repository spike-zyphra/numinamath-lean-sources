import Mathlib
theorem number_theory_610023 (a : ℕ) (ha : IsLeast {n : ℕ | n > 0 ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} a) : IsLeast {n : ℕ | n > a ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} 7:= by
  have h1 : a = 1 := by
    have h1 : a ∈ {n : ℕ | n > 0 ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} := by
      exact ha.1
    rcases h1 with ⟨ha_pos, ⟨k, hk⟩⟩
    have h3 : a ≥ 1 := by
      omega
    have h4 : a ≤ 1 := by
      have h5 : (1 : ℕ) ∈ {n : ℕ | n > 0 ∧ ∃ k : ℕ, n ^ 3 + n ^ 2 + n + 1 = k ^ 2} := by
        constructor
        · norm_num
        · use 2
          all_goals norm_num
      have h5' : a ≤ (1 : ℕ) := by
        apply ha.2
        exact h5
      omega
    linarith
  rw [h1]
  constructor
  · -- Show that 7 is in the set
    constructor
    · norm_num
    · use 20
      all_goals
      norm_num
  · -- Show that 7 is minimal in the set
    intro n hn
    rcases hn with ⟨hn1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have h2 : n ≤ 6 := by omega
    interval_cases n <;> try { 
      have h2k : k ≤ 32 := by nlinarith
      interval_cases k <;> omega 
    }