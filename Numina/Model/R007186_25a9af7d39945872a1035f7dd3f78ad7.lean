import Mathlib

theorem algebra_17241 {a b : ℝ} (ha : 2*a^2+6*a-14=0) (hb : 2*b^2+6*b-14=0)
    (h : a≠b) : (2*a-3)*(4*b-6)=-2 := by
  have h1 : 2 * a^2 + 6 * a - 14 = 0 := ha
  have h2 : 2 * b^2 + 6 * b - 14 = 0 := hb
  have h3 : 2 * (a^2 - b^2) + 6 * (a - b) = 0 := by 
    nlinarith
  have h4 : (a - b) * (2 * (a + b) + 6) = 0 := by 
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case $h5$: $a - b = 0$, hence $a = b$ which contradicts $a \neq b$.
    exfalso
    have h7 : a = b := by linarith
    exact h (by linarith)
  · -- Case $h6$: $2(a + b) + 6 = 0$, hence $a + b = -3$.
    have h7 : a + b = -3 := by linarith
    have h8 : a * b = -7 := by 
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by intro h'; apply h; linarith), sq_nonneg (a - b), sq_nonneg (a + b + 3)]
    have h9 : (2 * a - 3) * (4 * b - 6) = 8 * (a * b) - 12 * (a + b) + 18 := by 
      ring
    rw [h9]
    nlinarith [h7, h8]