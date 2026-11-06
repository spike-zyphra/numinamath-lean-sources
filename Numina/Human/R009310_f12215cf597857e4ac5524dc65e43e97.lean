import Mathlib

/- A lucky integer is a positive integer which is divisible by the sum of its digits. What is the least positive multiple of 9 that is not a lucky integer? -/
theorem algebra_14420 :
    IsLeast {n | 0 < n ∧ 9 ∣ n ∧ ¬n % (Nat.digits 10 n).sum = 0} 99 := by
  simp [IsLeast, lowerBounds]
  norm_num
  intro a h₀ h₁ h₂
  rw [dvd_def] at h₁
  obtain ⟨c, h₁⟩ := h₁
  rw [h₁]
  by_contra!
  replace this : c < 11 := by
    omega
  -- Consider numbers from 0 to 90 which are multiples of 9.
  interval_cases c
  . -- Case a = 0, impossible.
    linarith only [h₀, h₁]
  -- All other cases can be easily checked to be false.
  all_goals
    rw [h₁] at h₂
    simp at h₂
