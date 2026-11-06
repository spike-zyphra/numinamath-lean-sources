import Mathlib

theorem algebra_288602 {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (h1 : n * k + 38 = n * 9 - 3) : n = 41 := by
  have h2 : n * 9 ≥ 3 := by
    omega
  have eq1 : n * k + 38 + 3 = n * 9 := by
    omega 
  have h3 : n * 9 = n * k + 41 := by
    omega
  have h6 : n ∣ 41 := by
    have h12 : n ∣ (n * k + 41) := by
      have h13 : n * k + 41 = n * 9 := by
        omega
      have h14 : n ∣ n * 9 := by
        use 9
        all_goals
          ring
      rw [h13] at *
      exact h14
    have h13 : n ∣ n * k := by
      use k
      all_goals
        ring
    have h14 : n ∣ ((n * k + 41) - n * k) := by
      apply Nat.dvd_sub'
      · exact h12
      · exact h13
    have h15 : ((n * k + 41) - n * k) = 41 := by
      omega
    rw [h15] at h14
    exact h14
  have h7 : n = 1 ∨ n = 41 := by
    have h8 : n ∣ 41 := h6
    have h9 : n ≤ 41 := by
      exact Nat.le_of_dvd (by norm_num) h8
    interval_cases n <;> norm_num at h8 <;> tauto
  rcases h7 with (h8 | h9)
  · -- n = 1
    rw [show n = 1 by omega] at h3
    all_goals
      omega
  · -- n = 41
    omega