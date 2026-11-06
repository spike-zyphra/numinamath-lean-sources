import Mathlib

theorem number_theory_132544 (m n : ℕ) : m^2 + n^5 = 252 ↔ m = n ∧ n = 3 := by
  constructor
  · -- Forward direction: If $m^2 + n^5 = 252$, then $m = n$ and $n = 3$.
    intro h
    have h1 : n ≤ 3 := by
      by_contra h2
      push_neg at h2
      have h3 : n ^ 5 ≥ 1024 := by
        have h4 : n ≥ 4 := by linarith
        have h5 : n ^ 5 ≥ 4 ^ 5 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        norm_num at h5 ⊢
        linarith
      have h6 : m ^ 2 + n ^ 5 ≥ 1024 := by
        linarith [show n ^ 5 ≥ 1024 by linarith, show m ^ 2 ≥ 0 by positivity]
      linarith
    interval_cases n <;> try { 
      -- For each value of n, solve for m
      have h2 : m ≤ 15 := by
        nlinarith
      interval_cases m <;> omega 
    }
    <;> tauto
  · -- Backward direction: If $m = n$ and $n = 3$, then $m^2 + n^5 = 252$.
    rintro ⟨rfl, rfl⟩
    norm_num