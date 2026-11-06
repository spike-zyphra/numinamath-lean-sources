import Mathlib

theorem algebra_316987 {x1 x2 : ℝ} (hx1 : x1^2 + x1 - 3 = 0) (hx2 : x2^2 + x2 - 3 = 0)
    (hx12 : x1 ≠ x2) : x1^3 - 4 * x2^2 + 19 = 0 := by 
  have h1 : x1^2 + x1 - 3 = 0 := hx1
  have h2 : x2^2 + x2 - 3 = 0 := hx2
  have h3 : x1^2 - x2^2 + x1 - x2 = 0 := by 
    linarith
  have h4 : (x1 - x2) * (x1 + x2 + 1) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Show that $x1 = x2$ which is a contradiction
    exfalso
    apply hx12
    linarith
  · -- Show that $x1 + x2 + 1 = 0$ which means $x1 + x2 = -1$
    have h7 : x1 + x2 = -1 := by linarith
    have h8 : x1^2 = -x1 + 3 := by linarith
    have h9 : x1^3 = 4 * x1 - 3 := by
      calc
        x1^3 = x1 * x1^2 := by ring
        _ = x1 * (-x1 + 3) := by rw [h8]
        _ = -x1^2 + 3 * x1 := by ring
        _ = -(-x1 + 3) + 3 * x1 := by rw [h8]
        _ = x1 - 3 + 3 * x1 := by ring
        _ = 4 * x1 - 3 := by ring
    have h10 : x2^2 = -x2 + 3 := by linarith
    have h11 : 4 * x2^2 = -4 * x2 + 12 := by
      linarith [h10]
    have h12 : x1^3 - 4 * x2^2 + 19 = 0 := by
      linarith [h9, h11, h7]
    exact h12