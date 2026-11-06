import Mathlib

theorem algebra_247224 {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ d, x = a + d ∧ b = x + d ∧ 2 * x = b + d) :
    a / b = 1 / 3 := by 
  rcases h with ⟨d, hx1, hx2, hx3⟩
  have eq2 : b = a + 2 * d := by
    have eq1 : x = a + d := hx1
    linarith [hx2, eq1]

  have eq3 : 2 * (a + d) = (a + 2 * d) + d := by
    have eq1 : x = a + d := hx1
    have eq2' : b = a + 2 * d := eq2
    linarith [hx3, eq1, eq2']

  have ha_eq_d : a = d := by 
    linarith

  have hb_eq : b = 3 * a := by 
    rw [show d = a by linarith [ha_eq_d]] at eq2
    linarith

  have h1 : a / b = 1 / 3 := by
    rw [hb_eq]
    field_simp [ha]
    <;> linarith

  exact h1