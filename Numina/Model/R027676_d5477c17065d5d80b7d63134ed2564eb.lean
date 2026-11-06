import Mathlib

theorem algebra_99590 {m n p : ℝ} (h : m ≠ 0 ∧ n ≠ 0 ∧ p ≠ 0)
    (x y z : ℝ) (h1 : x / m = y / n) (h2 : y / n = z / p) :
    ∃ t, x = t * m ∧ y = t * n ∧ z = t * p := by
  have hm : m ≠ 0 := h.1
  have hn : n ≠ 0 := h.2.1
  have hp : p ≠ 0 := h.2.2

  use x / m 
  constructor
  · -- Show that x = t * m
    field_simp [hm]
  constructor
  · -- Show that y = t * n
    have h3 : x / m = y / n := h1 
    have h4 : x / m = y / n := h3 
    field_simp [hn, hm] at h4 ⊢ 
    <;> linarith 
  · -- Show that z = t * p 
    have h3 : y / n = z / p := h2 
    have h4 : x / m = z / p := by 
      linarith [h1, h2]
    have h5 : x / m = z / p := h4 
    field_simp [hp, hm] at h5 ⊢ 
    <;> linarith