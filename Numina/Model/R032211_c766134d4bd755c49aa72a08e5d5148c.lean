import Mathlib

theorem algebra_146735 (a b c x y : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h1 : a^3 + a * x + y = 0) (h2 : b^3 + b * x + y = 0) (h3 : c^3 + c * x + y = 0) :
    a + b + c = 0 := by
  have eq1 : a^3 + a * x + y - (b^3 + b * x + y) = 0 := by linarith
  have eq2 : a^3 - b^3 + a * x - b * x = 0 := by
    linarith [eq1]
  have eq3 : (a - b) * (a^2 + a * b + b^2 + x) = 0 := by
    ring_nf at eq2 ⊢
    linarith
  have h4 : a^2 + a * b + b^2 + x = 0 := by
    apply_fun (fun z => z / (a - b)) at eq3
    field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith)] at eq3 ⊢
    linarith
  have eq4 : b^3 + b * x + y - (c^3 + c * x + y) = 0 := by linarith
  have eq5 : b^3 - c^3 + b * x - c * x = 0 := by
    linarith [eq4]
  have eq6 : (b - c) * (b^2 + b * c + c^2 + x) = 0 := by
    ring_nf at eq5 ⊢
    linarith
  have h5 : b^2 + b * c + c^2 + x = 0 := by
    apply_fun (fun z => z / (b - c)) at eq6
    field_simp [(show b - c ≠ 0 by intro h; apply hb; linarith)] at eq6 ⊢
    linarith
  have eq7 : a^2 + a * b + b^2 - (b^2 + b * c + c^2) = 0 := by
    linarith [h4, h5]
  have eq8 : (a - c) * (a + b + c) = 0 := by
    ring_nf at eq7 ⊢
    linarith
  cases' (mul_eq_zero.mp eq8) with h6 h7
  · -- Case $a - c = 0$, so $a = c$
    exfalso
    exact hc (by linarith)
  · -- Case $a + b + c = 0$
    linarith