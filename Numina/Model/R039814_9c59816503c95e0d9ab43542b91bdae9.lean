import Mathlib

theorem number_theory_19571 :
    IsGreatest {x | ∃ a b, x = Nat.gcd a b ∧ a > 0 ∧ b > 0 ∧ a + b = 80} 40 := by
  constructor
  · -- Show that 40 is in the set
    use 40, 40
    all_goals norm_num
  · -- Show that 40 is the greatest
    intro x hx
    rcases hx with ⟨a, b, hx_eq, ha, hb, hsum⟩
    rw [hx_eq] at *
    have h1 : Nat.gcd a b ∣ a := by
      apply Nat.gcd_dvd_left
    have h2 : Nat.gcd a b ∣ b := by
      apply Nat.gcd_dvd_right
    have h3 : Nat.gcd a b ∣ a + b := by
      have h4 : Nat.gcd a b ∣ a := h1
      have h5 : Nat.gcd a b ∣ b := h2
      have h6 : Nat.gcd a b ∣ a + b := by
        exact Nat.dvd_add h4 h5
      exact h6
    have h4 : Nat.gcd a b ∣ 80 := by
      have h5 : a + b = 80 := hsum
      rw [h5] at h3
      exact h3
    have h5 : Nat.gcd a b ≤ 80 := by
      exact Nat.le_of_dvd (by norm_num) h4
    by_contra h
    push_neg at h
    have h6 : Nat.gcd a b ≥ 41 := by
      omega
    have h7 : Nat.gcd a b ∣ 80 := h4
    have h8 : Nat.gcd a b ≤ 80 := h5
    interval_cases h : Nat.gcd a b <;> norm_num at h7 h6 h8 ⊢
    all_goals omega