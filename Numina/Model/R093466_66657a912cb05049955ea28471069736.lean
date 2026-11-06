import Mathlib

theorem algebra_21426 : IsGreatest {x | x ∣ 99 ∧ x ∣ 100} 1 := by 
  constructor
  · -- Show that 1 belongs to the set
    constructor
    all_goals norm_num
  · -- Show that for any x in the set, x ≤ 1
    intro x h
    rcases h with ⟨h99, h100⟩
    have h1 : x ∣ 1 := by
      have h2 : x ∣ 100 := h100
      have h3 : x ∣ 99 := h99
      have h4 : x ∣ (100 : ℕ) - (99 : ℕ) := by
        apply Nat.dvd_sub' h2 h3
      have h5 : (100 : ℕ) - (99 : ℕ) = 1 := by norm_num
      rw [h5] at h4
      exact h4
    have hx : x ≤ 1 := by
      exact Nat.le_of_dvd (show 0 < 1 by norm_num) h1
    linarith