import Mathlib

theorem number_theory_325491 (n : ℤ) :
    (20 * n + 2) ∣ (2003 * n + 2002) ↔ n = 0 ∨ n = -42 := by
  constructor
  · -- If (20 * n + 2) divides (2003 * n + 2002), then n = 0 ∨ n = -42.
    intro h
    have h1 : (20 * n + 2) ∣ (2003 * n + 2002) := h
    have h2 : (20 * n + 2) ∣ (3 * n + 1802) := by
      have h3 : (20 * n + 2) ∣ (2003 * n + 2002) := h1
      have h4 : (20 * n + 2) ∣ (100 * (20 * n + 2)) := by
        use 100
        all_goals
          ring
      have h5 : (20 * n + 2) ∣ ((2003 * n + 2002) - 100 * (20 * n + 2)) := by
        exact Int.dvd_sub h3 h4
      have h5' : ((2003 * n + 2002) - 100 * (20 * n + 2)) = (3 * n + 1802) := by
        linarith
      rw [h5'] at h5
      exact h5
    have h3 : (20 * n + 2) ∣ (36034 : ℤ) := by
      have h4 : (20 * n + 2) ∣ (20 * (3 * n + 1802)) := by
        exact dvd_trans h2 (by simp)
      have h5 : (20 * n + 2) ∣ (3 * (20 * n + 2)) := by
        use 3
        all_goals
          ring
      have h6 : (20 * n + 2) ∣ (20 * (3 * n + 1802) - 3 * (20 * n + 2)) := by
        exact Int.dvd_sub h4 h5
      have h7 : (20 * (3 * n + 1802) - 3 * (20 * n + 2)) = (36034 : ℤ) := by
        nlinarith
      rw [h7] at h6
      exact h6
    have h4 : (20 * n + 2) ∣ (36034 : ℤ) := h3
    have h5 : (20 * n + 2) ≤ 36034 := by
      exact Int.le_of_dvd (by norm_num) h4
    have h6 : (20 * n + 2) ≥ -36034 := by
      have h7 : -(20 * n + 2) ∣ (36034 : ℤ) := by
        exact Int.neg_dvd.2 h4
      have h8 : -(20 * n + 2) ≤ 36034 := by
        exact Int.le_of_dvd (by norm_num) h7
      linarith
    have h7 : n ≤ 1801 := by
      omega
    have h8 : n ≥ -1802 := by
      omega
    interval_cases n <;> norm_num at h1 h4 ⊢
    all_goals
      omega
  · -- If n = 0 ∨ n = -42, then (20 * n + 2) divides (2003 * n + 2002).
    rintro (h | h)
    · -- When n = 0.
      rw [show n = (0 : ℤ) by linarith]
      norm_num
    · -- When n = -42.
      rw [show n = (-42 : ℤ) by linarith]
      norm_num