import Mathlib

theorem algebra_309241 {a b c p q : ℝ} (h : ∀ x, x^3 + p * x + q = (x - a) * (x - b) * (x - c))
    (hq : q ≠ 0) : (a^3 + b^3 + c^3) / (a * b * c) = 3 := by
  have h1 : a + b + c = 0 := by
    have eq1 := h 0
    have eq2 := h 1
    have eq3 := h 2
    have eq4 := h 3
    ring_nf at eq1 eq2 eq3 eq4 
    linarith
  have h2 : a * b + a * c + b * c = p := by
    have eq1 := h 0
    have eq2 := h 1
    have eq3 := h 2
    have eq4 := h 3
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have h3 : a * b * c = -q := by
    have eq1 := h 0
    ring_nf at eq1
    linarith
  have h4 : a * b * c ≠ 0 := by
    by_contra h0
    have : q = 0 := by 
      nlinarith [h3, h0]
    contradiction
  have h5 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    have h6 : a + b + c = 0 := h1
    have h7 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
      ring
    rw [h6] at h7
    have h8 : a^3 + b^3 + c^3 - 3 * (a * b * c) = 0 := by
      linarith
    linarith
  field_simp [h4]
  nlinarith [h5, h3]