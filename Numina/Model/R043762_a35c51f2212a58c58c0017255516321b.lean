import Mathlib

theorem algebra_306636 {a d e x1 x2 : ℝ} (ha : a ≠ 0) (hd : d ≠ 0)
    (h1 : a * (x1 - x1) * (x1 - x2) = d * x1 + e) (h2 : ∀ x, a * (x - x1) * (x - x2) + d * x + e = 0 → x = x1) :
    x2 - x1 = d / a := by

  have he : e = -d * x1 := by
    have eq1 : a * (x1 - x1) * (x1 - x2) = 0 := by
      simp
    linarith
  have eq8 := h2 (x2 - d / a) (by
    rw [he]
    field_simp [ha]
    <;> ring_nf 
    all_goals nlinarith
  )
  have eq9 : x2 - d / a = x1 := by 
    simpa using eq8 
  have eq10 : x2 - x1 = d / a := by 
    have eq11 : x2 - x1 = (x2 - d / a) - x1 + (d / a) := by 
      ring_nf 
    rw [eq11] 
    rw [eq9] 
    all_goals 
      field_simp [ha]
      <;> linarith 
  exact_mod_cast eq10