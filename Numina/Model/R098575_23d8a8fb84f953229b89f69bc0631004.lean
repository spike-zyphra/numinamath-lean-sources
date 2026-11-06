import Mathlib

theorem algebra_68443 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (a / b) * (c / d) = (a / b) + (c / d)) :
    b / a + d / c = 1 := by
  have h1 : a * c = a * d + b * c := by
    field_simp [hb, hd] at h
    linarith 
  have h2 : a * c ≠ 0 := by
    apply mul_ne_zero 
    exact ha 
    exact hc
  have h3 : b / a + d / c = (b * c + a * d) / (a * c) := by
    field_simp [ha, hc]
    <;> ring
  have h4 : b * c + a * d = a * c := by
    linarith [h1]
  rw [h3]
  rw [h4]
  field_simp [h2]
  all_goals linarith