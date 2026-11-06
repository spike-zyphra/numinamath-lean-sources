import Mathlib

theorem inequalities_7242 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    4 * a * b + b * c + c * a + 3 * c ≤ 9 := by
  have hc_eq : c = 3 - a - b := by linarith

  rw [hc_eq]
  
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (3 - a - b)), sq_nonneg (b - (3 - a - b))]