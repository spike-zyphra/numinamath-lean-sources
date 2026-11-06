import Mathlib

theorem number_theory_118440 (a d : ℕ) (hd : d ≠ 0) (ha : ∀ n, a + d * n > 0) :
    ¬ (∀ n, Nat.Prime (a + d * n)) := by 
  intro h
  have h1 := h 0
  have h2 := h a
  have h3 : Nat.Prime (a + d * a) := by
    simpa using h2
  have h4 : a + d * a = a * (1 + d) := by
    ring_nf
  rw [h4] at h3
  by_cases ha1 : a > 1
  · -- Assume a > 1. Then Nat.Prime a contradicts Nat.Prime (a * (1 + d))
    have h5 : Nat.Prime a := by
      simpa using h1
    have h7 : a > 1 := ha1
    have h8 : 1 + d > 1 := by
      have hd' : d > 0 := by
        by_contra h
        push_neg at h
        have h9 : d = 0 := by 
          omega
        contradiction
      omega
    -- Now Nat.Prime (a * (1 + d)) must hold, which is impossible for a > 1 and d > 0
    have h9 : ¬ Nat.Prime (a * (1 + d)) := by
      apply Nat.not_prime_mul (by omega) (by omega)
      all_goals linarith
    tauto
  · -- a ≤ 1
    have h3 : a ≤ 1 := by 
      omega
    have h4 : a = 0 ∨ a = 1 := by 
      interval_cases a <;> tauto
    rcases h4 with (h4 | h4)
    · -- a = 0 
      rw [h4] at h1 
      norm_num at h1 
      all_goals try tauto 
    · -- a = 1
      rw [h4] at h1 
      norm_num at h1 
      all_goals try tauto