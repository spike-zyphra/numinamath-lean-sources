import Mathlib

theorem algebra_143873 (a b c : ℕ) (h₀ : a^2 + b^2 + c^2 = 302) (h₁ : b = a + 1) (h₂ : c = b + 1) :
    max (max a b) c = 11 := by
  rw [h₁] at h₀ h₂
  rw [h₂] at h₀
  have h3 : a ≤ 17 := by
    nlinarith
  interval_cases a <;> norm_num at h₀ ⊢ <;> omega