import Mathlib

theorem algebra_14410 (d t1 t2 : ℝ) (h₀ : t1 = 10 / 60) (h₁ : t2 = 20 / 60)
    (h₂ : d / (t1 + t2) = 4) : d = 2 := by
  have ht : t1 + t2 = (1 / 2 : ℝ) := by
    rw [h₀, h₁]
    norm_num
  rw [ht] at h₂
  have h₄ : d ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
    all_goals linarith
  have h₅ : d = 2 := by
    field_simp [show (1 / 2 : ℝ) ≠ 0 by norm_num] at h₂
    linarith
  exact h₅
  all_goals linarith