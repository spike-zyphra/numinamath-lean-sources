import Mathlib

theorem algebra_255188 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 + a = b^2) (h2 : b^2 + b = c^2) (h3 : c^2 + c = a^2) :
    (a - b) * (b - c) * (c - a) = 1 := by
  have h4 : a + b + c = 0 := by
    nlinarith
  have eq1 : (a - b) * (a + b) = -a := by
    nlinarith
  have eq2 : (b - c) * (b + c) = -b := by
    nlinarith
  have eq3 : (c - a) * (c + a) = -c := by
    nlinarith
  have eq4 : a + b = -c := by
    linarith
  have eq5 : b + c = -a := by
    linarith
  have eq6 : c + a = -b := by
    linarith
  have eq7 : (a - b) = a / c := by
    have eq8 : (a - b) * (-c) = -a := by
      rw [show a + b = -c by linarith] at eq1
      linarith
    field_simp [hc] at eq8 ⊢
    <;> nlinarith
  have eq8 : (b - c) = b / a := by
    have eq9 : (b - c) * (-a) = -b := by
      rw [show b + c = -a by linarith] at eq2
      linarith
    field_simp [ha] at eq9 ⊢
    <;> nlinarith
  have eq9 : (c - a) = c / b := by
    have eq10 : (c - a) * (-b) = -c := by
      rw [show c + a = -b by linarith] at eq3
      linarith
    field_simp [hb] at eq10 ⊢
    <;> nlinarith
  calc
    (a - b) * (b - c) * (c - a) = (a / c) * (b / a) * (c / b) := by
      rw [eq7, eq8, eq9]
    _ = 1 := by
      field_simp [ha, hb, hc]
      <;> nlinarith