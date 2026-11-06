import Mathlib

theorem algebra_234384 (a b c d e : ℝ) (h₀ : a / b = 2 / 3) (h₁ : b / c = 3 / 4)
    (h₂ : c / d = 3 / 4) (h₃ : d / e = 4 / 5) :
    a / e = 3 / 10 := by
  have h4 : b ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have h5 : c ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have h6 : d ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
  have h7 : e ≠ 0 := by
    by_contra h
    rw [h] at h₃
    norm_num at h₃
  have h₄ : a / e = (a / b) * (b / c) * (c / d) * (d / e) := by
    field_simp [h4, h5, h6, h7]
    <;> ring
  rw [h₄, h₀, h₁, h₂, h₃]
  all_goals norm_num
  all_goals linarith