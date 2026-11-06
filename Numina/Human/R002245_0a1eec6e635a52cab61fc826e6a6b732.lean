import Mathlib

theorem number_theory_76050 : ¬∃ m n : ℤ, 19 * m ^ 2 + 95 * m * n + 2000 * n ^ 2 = 1995 := by
  rintro ⟨m, n, h⟩
  replace h : 19 * m ^ 2 = 1995 - 95 * m * n - 2000 * n ^ 2 := by linear_combination h
  have h₁ : 5 ∣ 1995 - 95 * m * n - 2000 * n ^ 2 := ⟨399 - 19 * m * n - 400 * n ^ 2, by ring⟩
  rw [← h] at h₁
  apply IsCoprime.dvd_of_dvd_mul_left (by norm_num) at h₁
  obtain ⟨k, rfl⟩ := Prime.dvd_of_dvd_pow (by norm_num) h₁
  replace h : 5 * (19 * k ^ 2 + 19 * k * n + 80 * n ^ 2) = 399 := by linarith only [h]
  have h₂ : 5 ∣ 5 * (19 * k ^ 2 + 19 * k * n + 80 * n ^ 2) := dvd_mul_right _ _
  rw [h] at h₂
  norm_num at h₂