import Mathlib

theorem inequalities_110143 {x y : ℝ} (h : x > y ∧ y > 2 / (x - y)) : x ^ 2 > y ^ 2 + 4 := by
  have h1 : x > y := h.1
  have h2 : y > 2 / (x - y) := h.2
  have hx2 : x - y > 0 := by linarith
  have h3 : y * (x - y) > 2 := by
    have h4 : x - y > 0 := hx2
    have h5 : y > 2 / (x - y) := h2
    have h6 : y * (x - y) > 2 := by
      have h7 : 2 / (x - y) < y := by linarith
      have h8 : 2 < y * (x - y) := by
        have pos1 : x - y > 0 := h4
        apply (div_lt_iff₀ pos1).mp at h7
        nlinarith
      linarith
    linarith
  have h7 : x ^ 2 - y ^ 2 > 4 := by
    nlinarith [sq_pos_of_pos hx2, sq_nonneg (x - y), sq_nonneg (y + 2), sq_nonneg (x - y - 2)]
  linarith