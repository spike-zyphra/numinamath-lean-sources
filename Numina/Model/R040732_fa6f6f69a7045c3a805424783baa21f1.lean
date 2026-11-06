import Mathlib

theorem number_theory_225803 (m n : ℕ) :
    m * n ^ 2 = 100 * (n + 1) ↔ (m = 200 ∧ n = 1) ∨ (m = 75 ∧ n = 2) ∨ (m = 24 ∧ n = 5) ∨ (m = 11 ∧ n = 10) := by

  constructor
  · -- Forward: if m * n^2 = 100 * (n + 1) then (m, n) must be one of the solutions
    intro h

    have h1 : n ≤ 100 := by
      by_contra h2
      push_neg at h2
      have h5 : n ≥ 101 := by omega
      have h2 : m * n ^ 2 = 100 * (n + 1) := h
      have h3 : m < 1 := by
        nlinarith [h2, h5, sq_pos_of_pos (show n > 0 by linarith)]
      have h4 : m = 0 := by omega
      rw [h4] at h
      all_goals
        nlinarith

    interval_cases n <;> try { 
      omega
    } <;> try { 
      have : m ≤ 200 := by nlinarith 
      interval_cases m <;> omega 
    }

  · -- Backward direction: each pair on the right side satisfies the equation
    rintro (h | h | h | h)
    · -- (200, 1)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (75, 2)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (24, 5)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (11, 10)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num