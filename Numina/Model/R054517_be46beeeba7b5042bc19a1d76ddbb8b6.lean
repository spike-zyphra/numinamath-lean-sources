import Mathlib

theorem algebra_234270 {a b c d : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : a / b = 2 / 3) (h2 : c / b = 1 / 5) (h3 : c / d = 7 / 15) :
    a * b / (c * d) = 70 / 9 := by

  have ha : a = 2 / 3 * b := by
    have h4 : a / b = 2 / 3 := h1
    field_simp [hb] at h4 ⊢
    linarith

  have hc_eq : c = 1 / 5 * b := by 
    have h4 : c / b = 1 / 5 := h2
    field_simp [hb] at h4 ⊢
    linarith
  
  have hd_eq : d = 15 / 7 * c := by 
    have h4 : c / d = 7 / 15 := h3
    field_simp [hd] at h4 ⊢
    linarith
  
  have hd_eq_b : d = 3 / 7 * b := by
    rw [hd_eq]
    rw [hc_eq]
    ring

  have hab : a * b = 2 / 3 * (b ^ 2) := by
    rw [ha]
    ring

  have hcd : c * d = 3 / 35 * (b ^ 2) := by
    rw [hc_eq, hd_eq_b]
    ring

  have h : b ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hb

  rw [hab, hcd]
  field_simp [h]
  <;> ring_nf
  <;> linarith