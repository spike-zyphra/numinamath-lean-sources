import Mathlib


theorem number_theory_81359 {n : ℕ} (hn : n ≥ 1) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ha : a ∣ n) (hb : b ∣ n) (h : a + b + a * b = n) : a = b := by

  have h1 : a ∣ n := ha
  have h2 : b ∣ n := hb

  have h7 : a ∣ (a * b + a + b) := by
    have h8 : a * b + a + b = n := by
      linarith
    rw [h8] 
    exact h1

  have h8 : a ∣ b := by
    have h9 : a ∣ (a * b + a + b) := h7
    have h10 : a ∣ (a * b + a) := by
      have h11 : a ∣ a * b := by
        use b
        all_goals ring_nf
      have h12 : a ∣ a := by
        exact dvd_refl a
      exact Nat.dvd_add h11 h12
    have h13 : a ∣ ((a * b + a + b) - (a * b + a)) := by
      apply Nat.dvd_sub' 
      · exact h9
      · exact h10
    have h14 : ((a * b + a + b) - (a * b + a)) = b := by
      omega
    rw [h14] at h13
    exact h13


  have h9 : b ∣ a := by
    have h10 : b ∣ (a * b + a + b) := by
      have h11 : a * b + a + b = n := by
        linarith
      rw [h11]
      exact h2
    have h11 : b ∣ (a * b + a + b) := h10
    have h12 : b ∣ (a * b + b) := by
      have h13 : b ∣ a * b := by
        use a
        all_goals ring_nf
      have h14 : b ∣ b := by
        exact dvd_refl b
      exact Nat.dvd_add h13 h14
    have h13 : b ∣ ((a * b + a + b) - (a * b + b)) := by
      apply Nat.dvd_sub' 
      · exact h11
      · exact h12
    have h14 : ((a * b + a + b) - (a * b + b)) = a := by
      omega
    rw [h14] at h13
    exact h13

  have h10 : a ≤ b := by
    exact Nat.le_of_dvd (by linarith) h8
  have h11 : b ≤ a := by
    exact Nat.le_of_dvd (by linarith) h9
  linarith