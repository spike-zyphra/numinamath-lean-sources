import Mathlib

theorem number_theory_318626 (p : ℕ) (hp : Nat.Prime p) (h : p + 3 ∣ 5 * p) :
    p ^ 2009 % 10 = 2 := by
  have h1 : p ≤ 5 := by
    by_contra h2
    push_neg at h2
    have h4 : p + 3 ∣ 5 * p := h
    have h5 : p + 3 ∣ 15 := by
      have h6 : p + 3 ∣ 5 * p := h4
      have h7 : p + 3 ∣ 5 * (p + 3) := by
        apply dvd_mul_of_dvd_right
        exact dvd_refl (p + 3)
      -- Since p + 3 divides 5 * p and 5 * (p + 3), it divides their difference
      have h8 : p + 3 ∣ (5 * (p + 3) - 5 * p) := by
        apply Nat.dvd_sub'
        · exact h7
        · exact h6
      have h9 : (5 * (p + 3) - 5 * p) = 15 := by
        omega
      rw [h9] at h8
      exact h8
    have h10 : p ≤ 12 := by
      have h11 : p + 3 ≤ 15 := by 
        exact Nat.le_of_dvd (by norm_num) h5
      omega
    interval_cases p <;> norm_num at hp h4 h5 ⊢ <;> all_goals tauto
  interval_cases p <;> norm_num at hp h ⊢ <;> norm_num [Nat.pow_mod]