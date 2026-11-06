import Mathlib

theorem algebra_308469 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (h : m * n + 9 * m + 11 * n + 145 = k * (m + 11)) (hk : k > 0)
    (h' : k * (m + 11) = k * (9 + n)) :
    k = 47 ∨ k = 25 := by
  have h_eq1 : m + 11 = 9 + n := by
    have h1 : k * (m + 11) = k * (9 + n) := h'
    have hk1 : k ≠ 0 := by linarith
    have h2 : m + 11 = 9 + n := by
      apply (mul_left_inj' hk1).mp
      linarith
    omega
  have h_eq2 : n = m + 2 := by
    omega
  rw [show n = m + 2 by linarith [h_eq2]] at h
  have eq1 : m ^ 2 + 22 * m + 167 = k * (m + 11) := by
    nlinarith
  have eq3 : (m + 11) ∣ 46 := by
    have eq7 : (m + 11) ∣ k * (m + 11) := by
      use k
      all_goals ring
    have eq8 : (m + 11) ∣ (m + 11) ^ 2 := by
      use (m + 11)
      all_goals ring
    have eq9 : (m + 11) ∣ (k * (m + 11) - (m + 11) ^ 2) := by
      apply Nat.dvd_sub'
      · exact eq7
      · exact eq8
    have eq10 : (k * (m + 11) - (m + 11) ^ 2) = 46 := by
      have eq3 : k * (m + 11) = (m + 11) ^ 2 + 46 := by
        nlinarith [eq1]
      omega
    rw [eq10] at eq9
    exact eq9
  have h4 : (m + 11) = 23 ∨ (m + 11) = 46 := by
    have h5 : (m + 11) ∣ 46 := eq3
    have h6 : (m + 11) ≤ 46 := by
      exact Nat.le_of_dvd (by linarith) h5
    have h7 : (m + 11) ≥ 12 := by
      omega
    interval_cases h8 : (m + 11) <;> try { tauto }
  rcases h4 with (h4 | h4)
  · -- Assume m + 11 = 23
    have h8 : m + 11 = 23 := by
      omega
    have h9 : m = 12 := by
      omega
    have h10 : k = 25 := by
      rw [show m = 12 by linarith [h9]] at eq1
      omega
    right
    omega
  · -- Assume m + 11 = 46
    have h8 : m + 11 = 46 := by
      omega
    have h9 : m = 35 := by
      omega
    have h10 : k = 47 := by
      rw [show m = 35 by linarith [h9]] at eq1
      omega
    left
    omega