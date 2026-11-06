import Mathlib

/- When the length of a rectangle is increased by $20\%$ and the width increased by $10\%$, by what percent is the area increased? -/
theorem algebra_13726 {l w nl nw : ℝ} (hl : 0 < l ∧ 0 < nl) (hw : 0 < w ∧ 0 < nw)
    (h : nl = 1.2 * l ∧ nw = 1.1 * w) :
    (nl * nw - l * w) / (l * w) = 0.32 := by
  simp_all
  ring_nf
  rw [mul_right_comm l, mul_inv_cancel_right₀, mul_inv_cancel₀, one_mul]
  <;> linarith