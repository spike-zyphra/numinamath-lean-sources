import Mathlib

theorem algebra_189675 (total_score other_total_score xiao_ming_score : ℝ)
    (h₀ : total_score = 84 * 10) (h₁ : other_total_score = total_score - xiao_ming_score)
    (h₂ : xiao_ming_score = 93) :
    other_total_score / 9 = 83 := by
  have h3 : other_total_score = 747 := by
    rw [h₁, h₀, h₂]
    norm_num
  rw [h3]
  norm_num