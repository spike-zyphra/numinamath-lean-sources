import Mathlib

/-For what value of $c$ will the circle with equation $x^2 - 10x + y^2 + 6y + c = 0$ have a radius of length 1?-/
theorem algebra_22104 (c : ℝ) (h : ∃a b, ∀ x y, x ^ 2 - 10 * x + y ^ 2 + 6 * y + c = 0 ↔ (x - a) ^ 2 + (y - b) ^ 2 = 1) :
    c = 33 := by
  obtain ⟨a, b, h⟩ := h
  -- show that a = 5
  have ha : a = 5 := by
    have h1 := h (a + 1) b
    have h2 := h (a - 1) b
    simp at h1 h2
    ring_nf at h1 h2
    -- actually subtract two expressions
    calc
      a = (4 * a - 20) / 4 + 5 := by ring_nf
      _ = ((-9 - a * 8 + a ^ 2 + b * 6 + b ^ 2 + c) - (11 - a * 12 + a ^ 2 + b * 6 + b ^ 2 + c)) / 4 + 5 := by ring_nf
      _ = (0 - 0) / 4 + 5 := by rw [h1, h2]
      _ = 5 := by norm_num
  -- show that b = -3
  have hb : b = -3 := by
    have h1 := h a (b + 1)
    have h2 := h a (b - 1)
    simp at h1 h2
    ring_nf at h1 h2
    -- subtract two expressions
    calc
      b = (4 * b + 12) / 4 - 3 := by ring_nf
      _ = ((7 - a * 10 + a ^ 2 + b * 8 + b ^ 2 + c) - (-5 - a * 10 + a ^ 2 + b * 4 + b ^ 2 + c)) / 4 - 3 := by ring_nf
      _ = (0 - 0) / 4 - 3 := by rw [h1, h2]
      _ = -3 := by norm_num
  -- substitute a = 5, b = -3, x = 5, y = -2
  -- so that we simplify the expression to -33 + c = 0
  have hc := h 5 (-2)
  rw [ha, hb] at hc
  ring_nf at hc
  simp at hc
  linarith only [hc]