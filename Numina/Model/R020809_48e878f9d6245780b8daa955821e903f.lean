import Mathlib

theorem number_theory_271398 (N : ℤ) :
    (N^2 - 71) % (7 * N + 55) = 0 ↔ N = 57 ∨ N = -8 := by
  constructor
  · -- Assume (N^2 - 71) % (7 * N + 55) = 0, prove N = 57 ∨ N = -8
    intro h
    have h1 : (7 * N + 55) ∣ (N^2 - 71) := by 
      exact Int.dvd_of_emod_eq_zero h
    by_cases h2 : (7 * N + 55) = 0
    · -- If 7 * N + 55 = 0, then 7 * N = -55, so N = -55/7 which is not integer. Contradiction.
      -- But we need to formalize that in Lean
      have h3 : 7 * N = -55 := by linarith
      omega 
    · -- Assume 7 * N + 55 ≠ 0
      -- Now we can use the fact that (7 * N + 55) divides (N^2 - 71)
      -- So we can express that (7 * N + 55) divides some value
      have h4 : (7 * N + 55) ∣ (49 * (N ^ 2 - 71) - (7 * N + 55) * (7 * N - 55)) := by 
        apply Dvd.dvd.sub
        · -- Show that (7 * N + 55) divides 49*(N^2 - 71)
          have h5 : (7 * N + 55) ∣ (49 * (N ^ 2 - 71)) := by
            have h6 : (7 * N + 55) ∣ (N ^ 2 - 71) := h1
            apply dvd_trans h6
            norm_num 
          exact h5 
        · -- Show that (7 * N + 55) divides (7 * N + 55) * (7 * N - 55)
          use (7 * N - 55)
          all_goals ring_nf <;> omega
      have h5 : (7 * N + 55) ∣ (454 : ℤ) := by 
        have h6 : (7 * N + 55) ∣ (49 * (N ^ 2 - 71) - (7 * N + 55) * (7 * N - 55)) := h4 
        have h7 : (49 * (N ^ 2 - 71) - (7 * N + 55) * (7 * N - 55)) = -454 := by 
          nlinarith 
        rw [h7] at h6 
        have h8 : (7 * N + 55) ∣ (-454 : ℤ) := by 
          exact h6 
        have h9 : (7 * N + 55) ∣ (454 : ℤ) := by 
          exact Int.dvd_neg.mp h8 
        exact h9 
      have h6 : (7 * N + 55) ≤ 454 := by 
        apply Int.le_of_dvd (by norm_num) h5 
      have h7 : (7 * N + 55) ≥ -454 := by
        have h8 : -(7 * N + 55) ∣ (454 : ℤ) := by 
          exact Int.neg_dvd.2 h5 
        have h9 : -(7 * N + 55) ≤ 454 := by 
          apply Int.le_of_dvd (by norm_num) h8 
        omega 
      have h8 : N ≤ 63 := by
        omega 
      have h9 : N ≥ -87 := by
        omega 
      interval_cases N <;> norm_num at h1 h ⊢ 
      <;> omega 
  · -- Assume N = 57 ∨ N = -8, prove (N^2 - 71) % (7 * N + 55) = 0
    rintro (h | h)
    · -- N = 57
      rw [h]
      norm_num 
    · -- N = -8
      rw [h]
      norm_num