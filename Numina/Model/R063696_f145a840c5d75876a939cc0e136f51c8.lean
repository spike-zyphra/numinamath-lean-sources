import Mathlib

theorem algebra_121208 {a b c : ℝ} (ha : a < 0) (hb : b < 0) (hc : c < 0)
    (h1 : c / (a + b) = 2) (h2 : c / (b - a) = 3) : a > c := by
  have h1' : a + b ≠ 0 := by 
    by_contra h
    rw [h] at h1
    norm_num at h1 
  have h2' : b - a ≠ 0 := by 
    by_contra h
    rw [h] at h2
    norm_num at h2 
  have eq1 : c = 2 * (a + b) := by 
    have h : a + b ≠ 0 := h1'
    field_simp [h] at h1 
    linarith 
  have eq2 : c = 3 * (b - a) := by 
    have h : b - a ≠ 0 := h2'
    field_simp [h] at h2 
    linarith 
  have h3 : b = 5 * a := by 
    linarith [eq1, eq2] 
  have c_eq : c = 12 * a := by 
    rw [show b = 5 * a by linarith [h3]] at eq1 
    linarith 
  linarith [c_eq, ha]