import Mathlib

theorem algebra_98891 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h1 : (l + 6) * (w - 2) = l * w) (h2 : (l - 12) * (w + 6) = l * w)
    (h3 : 2 * (l + w) = x) :
    x = 132 := by
  have eq1 : -2 * l + 6 * w = 12 := by
    nlinarith

  have eq2 : 6 * l - 12 * w = 72 := by
    nlinarith
  
  have hw_eq : w = 18 := by
    linarith [eq1, eq2]

  have hl_eq : l = 48 := by
    linarith [eq1, hw_eq]

  have hx : x = 2 * (l + w) := by linarith [h3]
  
  rw [hl_eq, hw_eq] at hx
  norm_num at hx
  
  linarith