import Mathlib

theorem algebra_322324 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ∃ x, x^2 + 2 * a * x + b^2 = 0 ∧ x^2 + 2 * c * x - b^2 = 0)
    (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) :
    a^2 + b^2 = c^2 ∨ b^2 + c^2 = a^2 ∨ c^2 + a^2 = b^2 := by
  rcases h with ⟨x, h₁, h₂⟩
  have eq1 : x^2 + 2 * a * x + b^2 = 0 := h₁
  have eq2 : x^2 + 2 * c * x - b^2 = 0 := h₂
  have eq3 : 2 * a * x + 2 * b^2 - 2 * c * x = 0 := by
    nlinarith [h₁, h₂]
  have eq4 : (a - c) * x + b^2 = 0 := by
    nlinarith [h₁, h₂]
  have eq5 : (a - c) * x = -b^2 := by
    linarith [eq4]
  by_cases hne : a - c = 0
  · -- suppose a - c = 0
    have heq5 : a - c = 0 := hne
    have eq6 : (a - c) * x = -b^2 := eq5
    rw [show a - c = 0 by linarith [heq5]] at eq6
    have eq7 : b^2 = 0 := by
      nlinarith 
    have eq8 : b = 0 := by
      nlinarith
    linarith
  · -- a - c ≠ 0
    have hne' : a - c ≠ 0 := by
      intro h'
      apply hne
      linarith
    have eq8 : x = -b^2 / (a - c) := by
      have hne : a - c ≠ 0 := hne'
      field_simp [hne']
      linarith [eq5]
    have eq9 : b^2 * (c^2 + b^2 - a^2) = 0 := by
      rw [eq8] at eq1
      field_simp [(show (a - c) ≠ 0 by exact hne')] at eq1
      nlinarith [sq_pos_of_pos hb, sq_pos_of_pos ha, sq_pos_of_pos hc]
    cases' (mul_eq_zero.mp eq9) with h10 h11
    · -- h10: b^2 = 0
      have h12 : b^2 = 0 := by
        nlinarith
      have h13 : b = 0 := by
        nlinarith
      linarith
    · -- h11 : c^2 + b^2 - a^2 = 0
      have h12 : c^2 + b^2 = a^2 := by
        linarith
      right
      left
      linarith