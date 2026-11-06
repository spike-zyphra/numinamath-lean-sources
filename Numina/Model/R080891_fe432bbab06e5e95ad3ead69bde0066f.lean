import Mathlib

theorem algebra_299689 {y1 y2 : ℝ → ℝ} (hy1 : ∃ c, ∀ x, y1 x = c / x)
    (hy2 : ∃ d, ∀ x, y2 x = d * (x - 2)) (h1 : y1 1 - y2 1 = -1)
    (h2 : y1 (-3) = y2 (-3) - 21) :
    y1 (-5) - y2 (-5) = -28.6 := by 
  rcases hy1 with ⟨c, hy1⟩
  rcases hy2 with ⟨d, hy2⟩
  have eq1 : y1 1 - y2 1 = -1 := h1
  have eq2 : y1 (-3) = y2 (-3) - 21 := h2
  rw [hy1, hy2] at eq1 eq2
  norm_num at eq1 eq2
  have hc : c = 3 := by 
    linarith 
  have hd : d = -4 := by 
    linarith [hc]
  have h3 : y1 (-5) - y2 (-5) = -28.6 := by
    rw [hy1, hy2]
    rw [hc, hd]
    norm_num
  exact h3