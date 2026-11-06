import Mathlib

theorem number_theory_193962 (n : ℕ) (h₀ : n > 0) (h₁ : (10 * n + 4) % (n + 4) = 0)
    (h₂ : (10 * n + 4) / (n + 4) = (n + 4) - 27) :
    n = 32 := by
  have h3 : (n + 4) ∣ (10 * n + 4) := by
    exact Nat.dvd_of_mod_eq_zero h₁
  have h4 : (n + 4) ∣ 36 := by
    have h5 : (n + 4) ∣ (10 * n + 4) := h3
    have h6 : (n + 4) ∣ (10 * (n + 4)) := by
      use 10
      all_goals ring_nf <;> omega
    have h7 : (n + 4) ∣ ((10 * (n + 4)) - (10 * n + 4)) := by
      apply Nat.dvd_sub'
      · exact h6
      · exact h5
    have h8 : ((10 * (n + 4)) - (10 * n + 4)) = 36 := by
      simp [Nat.mul_add, add_mul, mul_add, add_assoc]
      <;> ring_nf <;> omega
      all_goals ring_nf <;> omega
    rw [h8] at h7
    exact h7
  have h5 : (n + 4) ≤ 36 := by
    exact Nat.le_of_dvd (show (0 : ℕ) < 36 by norm_num) h4
  have h6 : n ≤ 32 := by
    omega
  interval_cases n <;> norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  all_goals norm_num at h₀ h₁ h₂
  <;> omega
  <;> omega