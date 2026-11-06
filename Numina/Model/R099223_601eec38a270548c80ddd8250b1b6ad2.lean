import Mathlib

theorem number_theory_4643 {n b : ℕ} (hb : 6 < b ∧ b < 10)
    (h₁ : Nat.ofDigits b [1, 4, 4] = n ^ 2) (h₂ : Nat.ofDigits b [1, 5, 3] = (n - 2) ^ 2) :
    n = 19 := by
  rcases hb with ⟨hb1, hb2⟩
  simp [Nat.ofDigits, List.foldl] at h₁ h₂
  have h3 : b = 7 ∨ b = 8 ∨ b = 9 := by 
    have h4 : b ≤ 9 := by linarith
    have h5 : b ≥ 7 := by linarith
    interval_cases b <;> omega
  rcases h3 with h3 | h3 | h3
  · -- Check b = 7
    rw [h3] at h₁ h₂ 
    norm_num at h₁ h₂ 
    have : n ≤ 17 := by nlinarith
    interval_cases n <;> omega
  · -- Check b = 8
    rw [h3] at h₁ h₂ 
    norm_num at h₁ h₂ 
    have : n ≤ 17 := by nlinarith
    interval_cases n <;> omega
  · -- Check b = 9
    rw [h3] at h₁ h₂ 
    norm_num at h₁ h₂ 
    have : n ≤ 21 := by nlinarith
    interval_cases n <;> omega