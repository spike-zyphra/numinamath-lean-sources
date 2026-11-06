import Mathlib

theorem algebra_10850 (n : ℕ) (h₀ : n = 3544 ∨ n = 3554 ∨ n = 3564 ∨ n = 3572 ∨ n = 3576) (h₁ : ¬4 ∣ n) :
    (n % 10) * ((n / 10) % 10) = 20 := by
  rcases h₀ with (rfl | rfl | rfl | rfl | rfl)
  · norm_num at h₁ 
  · norm_num
  · norm_num at h₁ 
  · norm_num at h₁ 
  · norm_num at h₁