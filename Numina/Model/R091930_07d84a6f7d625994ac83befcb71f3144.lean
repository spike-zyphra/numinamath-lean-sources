import Mathlib

theorem algebra_235265 {a b c : ℝ} (h : a^2 + b = b^2 + c ∧ b^2 + c = c^2 + a) :
    a * (a^2 - b^2) + b * (b^2 - c^2) + c * (c^2 - a^2) = 0 := by
  have h1 : a^2 + b = b^2 + c := h.1
  have h2 : b^2 + c = c^2 + a := h.2
  have h3 : a^2 - b^2 = c - b := by
    linarith
  have h4 : b^2 - c^2 = a - c := by 
    linarith
  have h5 : c^2 - a^2 = b - a := by
    linarith
  -- substitute these equalities into the original expressions
  calc
    a * (a^2 - b^2) + b * (b^2 - c^2) + c * (c^2 - a^2)
        = a * (c - b) + b * (a - c) + c * (b - a) := by
          rw [show a^2 - b^2 = c - b by linarith, 
              show b^2 - c^2 = a - c by linarith, 
              show c^2 - a^2 = b - a by linarith]
          <;> ring_nf <;> nlinarith
    _ = a * c - a * b + b * a - b * c + c * b - c * a := by
          ring_nf
    _ = 0 := by
          ring_nf <;> nlinarith