import Mathlib

theorem algebra_99914 {a b c p q : ℝ} (h : ∀ x, x^3 + p * x + q = (x - a) * (x - b) * (x - c)) (hq : q ≠ 0) :
    (a^3 + b^3 + c^3) / (a * b * c) = 3 := by

  have h1 : a + b + c = 0 := by
    have eq1 := h 0
    have eq2 := h 1
    have eq3 := h (-1)
    have eq4 := h 2
    norm_num at eq1 eq2 eq3 eq4
    nlinarith [sq_pos_of_ne_zero hq]

  have h2 : a * b * c = -q := by
    have eq1 := h 0
    norm_num at eq1
    nlinarith

  have h4 : a * b + b * c + c * a = p := by
    have eq1 := h 1
    have eq2 := h (-1)
    have eq3 := h 2
    norm_num at eq1 eq2 eq3
    nlinarith [sq_pos_of_ne_zero hq]

  have h5 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by
    have h6 : a + b + c = 0 := h1
    have h7 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by
      ring
    rw [h6] at h7
    have h8 : a^3 + b^3 + c^3 - 3 * (a * b * c) = 0 := by
      linarith
    linarith

  have h6 : a * b * c ≠ 0 := by
    intro h
    have : q = 0 := by
      linarith [h2, h]
    contradiction

  field_simp [h6]
  nlinarith [h5, h2, hq]