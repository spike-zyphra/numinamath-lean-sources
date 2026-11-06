import Mathlib

theorem algebra_257604 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : (5 * a + b) / (5 * c + d) = (6 * a + b) / (6 * c + d)) (h2 : (7 * a + b) / (7 * c + d) = 9) :
    (9 * a + b) / (9 * c + d) = 9 := by
  have h1' : 5 * c + d ≠ 0 := by
    nlinarith
  have h1'' : 6 * c + d ≠ 0 := by
    nlinarith
  have eq1 : (5 * a + b) * (6 * c + d) = (6 * a + b) * (5 * c + d) := by
    have h11 : (5 * a + b) / (5 * c + d) = (6 * a + b) / (6 * c + d) := h1
    field_simp [h1', h1''] at h11 ⊢
    linarith
  have h_eq : b * c = a * d := by
    linarith [eq1]
  have h2' : 7 * c + d ≠ 0 := by 
    nlinarith
  have eq2 : 7 * a + b = 9 * (7 * c + d) := by
    have h22 : (7 * a + b) / (7 * c + d) = 9 := h2
    field_simp [h2'] at h22 ⊢
    linarith
  have eq3 : (7 * c + d) * (9 * c - a) = 0 := by
    have hb_eq : b = 63 * c + 9 * d - 7 * a := by linarith [eq2]
    rw [hb_eq] at h_eq
    nlinarith
  cases (mul_eq_zero.mp eq3) with
  | inl h11 =>
    nlinarith
  | inr h4 =>
    have ha_eq : a = 9 * c := by linarith
    have hb_eq : b = 9 * d := by
      rw [ha_eq] at eq2
      nlinarith
    have h3 : 9 * a + b = 9 * (9 * c + d) := by
      rw [ha_eq]
      nlinarith [hb_eq]
    have h4' : 9 * c + d ≠ 0 := by
      nlinarith
    rw [show 9 * a + b = 9 * (9 * c + d) by nlinarith [h3]]
    field_simp [h4']
    <;> nlinarith