import Mathlib

theorem algebra_307262 (a b c d t : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 1 / a + 1 / b = 1 / 10)
    (h₄ : 1 / a = 1 / 12 )
    (h₂ : 1 / c + 1 / d = 1 / 12)
    (h₃ : 1 / d = 1 / 20) (ht : t = c + (1 - c * (1 / b) ) / (1 / a + 1 / b)):
    t = 35 := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have ha' : a = 12 := by 
    field_simp at h₄
    nlinarith
  have hd' : d = 20 := by
    field_simp at h₃
    nlinarith
  have ha1 : 1 / a = 1 / 12 := by
    linarith [h₄]
  have hb1 : 1 / b = 1 / 60 := by
    have hb2 : b = 60 := by
      rw [show a = 12 by linarith [ha']] at h₁
      field_simp at h₁
      nlinarith
    rw [hb2]
    all_goals norm_num 
  have hc' : c = 30 := by
    rw [show d = 20 by linarith [hd']] at h₂
    field_simp at h₂ 
    nlinarith
  rw [ht]
  have h9 : 1 / a + 1 / b = 1 / 10 := by 
    linarith [h₁]
  rw [show c = 30 by linarith [hc']]
  have eq1 : (1 - (30 : ℝ) * (1 / b) ) = (1 / 2 : ℝ) := by
    rw [show 1 / b = 1 / 60 by linarith [hb1]]
    norm_num
  rw [eq1]
  rw [h9]
  norm_num